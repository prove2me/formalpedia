-- Prove2me | Definitions.Def_QMCLeafB_truebit_m5
-- name    : QMCLeafB_truebit_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:16:07.58796+00:00
-- url     : https://prove2.me/theorems/11c8d037-ac04-44d0-b8dd-3dfccd5695cf
-- title:
--   QMCLeafB truebit_m5
-- statement:
--   # `Check_truebit_m5` — phase 25, member m5, direction `truebit-runparts`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thrice
import Definitions.Def_QMCLeafB_hemptyR
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_anchorfacts
/-
# `Check_truebit_m5` — phase 25, member m5, direction `truebit-runparts`

**The true-bit production, at the leaf's own interface, and what it does to the phase-25
architecture.**

`Check_thrice_m3` splits the residual into

* `TripleSupply.trueBit` — `CoreDataG` at every interior point whose program bit is `true`;
* `TripleSupply.third`   — `RunParts` at every interior point with a nonempty body and a `false` bit.

The first slot is stated at the *conduit* shape `CoreDataG`, whose `hmem` field lives at the
**pinched** centre `cXst` (diagonal `1 − dq/4` by definition).  At the sliver `(G₁, t₁)` the body is
nonempty and yet no pinched matrix is a member, so `CoreDataG` is uninhabited there for *every* bit
(`AnchorFactsM2.not_coreDataG_G₁`).  Since the second slot is also dead there whenever the bit reads
`false` (`BallM2.sliver_bit_true` forces the bit `true`), the phase-25 `TripleSupply` is **empty for
every program bit** (§3) — the fourth recurrence of the vacuity defect.

The repair is not analytic: `RunParts` at a `true` bit costs **one certificate and nothing else**.
Its `hcert` field is exactly "a unit-diagonal PSD matrix within the leaf's mint tolerance
`t + Rq/40000`", and with `ok ≡ true` every cut-side field is vacuous.  So:

* §1 `MintCert` / `runParts_of_mintCert` — a bit-true interior point plus one mint certificate gives
  `RunParts`, with no pinch, no `CoreDataG`, no run invariant, no drift budget;
* §2 the two anchors: the sliver `(G₁, t₁)` (banked witness `!![1,-1;-1,1]`, `BallM2`) and
  `(G₀, −1/2)` (via the banked ok-point) both produce `RunParts` at the `true` bit;
* §3 `not_tripleSupply` — the phase-25 `TripleSupply` is uninhabited at `paramsKbc2` for every bit;
* §4 `TripleSupplyR` — the same split with the `true`-bit slot stated at `RunParts` (strictly weaker,
  and inhabited at the sliver), plus the full stroke to the verbatim `d9f601e5` sentence;
* §5 conservativity: every `TripleSupply` producer is a `TripleSupplyR` producer (§7 keeps the
  conduit lane plugged in), so nothing banked is lost;
* §6 `residParts_of_design` — the exact shape of what is still owed: at a nonempty body the design
  must read `true` **and** carry a mint certificate; then `ResidParts` follows from the campaign data
  alone and **no third stratum is owed**.  `MintCert` at every nonempty body is the single geometric
  statement the leaf's `4ε` mint budget exists to buy.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` on every declaration, expected `[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.TrueBitM5

open QuantumMaxCutEnergy

/-! ## 1.  The mint certificate, and `RunParts` from it

`RunParts.hcert` is the leaf's own `ok`-round certificate: a unit-diagonal PSD matrix whose objective
is within the **mint** tolerance `t + Rq/40000`.  That is a strictly weaker demand than the campaign's
`RelaxMem` at the pinched diagonal (which asks for the same at the *engine's* level `t − ε` on the
diagonal `1 − dq/4`).  With `ok ≡ true`, all seven cut-side fields are vacuous, so one certificate
produces the run record. -/

/-- **The mint certificate**: one unit-diagonal PSD matrix within the leaf's own tolerance. -/
def MintCert (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
      (QMCLeafB.wMatrix G * X).trace
        ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)

/-- **A positive horizon.**  `paramsKbc2`'s round count is at least one (`Kbc2 ≥ 1`, `mHalve ≥ 1`). -/
theorem one_le_km (G : QuantumMaxCutEnergy.Input) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m :=
  lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul G)

/-- **The true-bit production.**  At any `(G, t, P)` whose program bit is `true`, one mint
certificate gives the leaf's whole record `RunParts`: report `ok` at every round below the horizon
(the only field with content is `hcert`, and it is the certificate itself), and the verdict equation
is `anyOk (fun _ => true) (K·m) = true` because the horizon is positive.

Nothing else is used: no pinched member, no `CoreDataG`, no run invariant, no drift budget, no margin,
no normal, no separation oracle. -/
noncomputable def runParts_of_mintCert {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hKm : 0 < P.K * P.m) (hT : o G t = true) (h : MintCert G t) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  classical
  set X : Matrix (Fin G.n) (Fin G.n) ℝ := Classical.choose h with hXdef
  have hX : QMCLeafB.AnswerProducer.IsUnitDiagPSD X := (Classical.choose_spec h).1
  have htr : (QMCLeafB.wMatrix G * X).trace
      ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := (Classical.choose_spec h).2
  refine
    { ok := fun _ => true
      cd := fun _ => ⟨0, 0, 0⟩
      del := fun _ => 0
      hcert := ?_
      hwit := ?_
      hrho := ?_
      hcne := ?_
      hdel0 := ?_
      hcheck := ?_
      hle := ?_
      hcut := ?_
      hverdict := ?_ }
  · intro k _hk _hok
    exact ⟨X, hX, htr⟩
  · intro k _hk hok
    exact absurd hok (by simp)
  · intro k _hk hok
    exact absurd hok (by simp)
  · intro k _hk hok
    exact absurd hok (by simp)
  · intro k _hk hok
    exact absurd hok (by simp)
  · intro k _hk hok
    exact absurd hok (by simp)
  · intro k _hk hok
    exact absurd hok (by simp)
  · intro k _hk hok
    exact absurd hok (by simp)
  · rw [hT]
    exact ((QMCLeafB.SimLoop.anyOk_eq_true_iff (fun _ => true) (P.K * P.m)).2
      ⟨0, hKm, rfl⟩).symm

#print axioms QMCLeafB.TrueBitM5.runParts_of_mintCert

/-! ## 2.  Two anchors: the sliver at the `true` bit, and `(G₀, −1/2)`

The sliver's ball obstruction (`BallM2.no_runParts_of_ball`) forbids only the **`false`** bit there.
At the `true` bit the leaf's own certificate exists (`BallM2.sliver_hcert_witness`, the rank-one point
`!![1,-1;-1,1]` with objective `−2`), so `RunParts` is *inhabited* at `(G₁, t₁)`.  This is the
machine-checked form of "the sliver is not dead, it is a `true`-bit point". -/

/-- **`RunParts` at the sliver, at the `true` bit.** -/
noncomputable def runParts_sliver_trueBit :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => true) QMCLeafB.AnchorFactsM2.G₁
      QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.P₁ :=
  runParts_of_mintCert (one_le_km _) rfl QMCLeafB.BallM2.sliver_hcert_witness

#print axioms QMCLeafB.TrueBitM5.runParts_sliver_trueBit

/-- **`RunParts` at the ok anchor `(G₀, −1/2)`,** through the conduit lane that is *alive* there
(`OkProd_M8.coreDataG_G₀_half_via_okprod`).  Together with the sliver this shows that the mint route
and the pinch route agree wherever the pinch route exists. -/
noncomputable def runParts_G₀_half_trueBit :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  QMCLeafB.ThriceM3.runParts_of_coreDataG (G := QMCLeafB.ResidRefute.G₀) (t := -(1 / 2))
    (hn := QMCLeafB.ResidKill.hnG₀)
    (by rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num)
    (by rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num)
    (Classical.choice QMCLeafB.OkProd_M8.coreDataG_G₀_half_via_okprod)

#print axioms QMCLeafB.TrueBitM5.runParts_G₀_half_trueBit

/-! ## 3.  The refutation: the phase-25 `TripleSupply` is empty at `paramsKbc2`

At the sliver the body is nonempty, so both slots are demanded:

* if the bit is `true`, `trueBit` asks for `CoreDataG` — impossible for every bit
  (`AnchorFactsM2.not_coreDataG_G₁`);
* if the bit is `false`, `third` asks for `RunParts` — impossible, since any `RunParts` at the sliver
  forces the bit `true` (`BallM2.sliver_bit_true`, the campaign ball).

So no `TripleSupply` producer can exist, for any program bit.  The vacuity is structural: it is the
**conduit shape** at a pinched-infeasible point, not the stratum, that kills it. -/

/-- **The sliver is not `BodyEmpty`** (from the banked real witness `AnchorFactsM2.realBody_G₁`). -/
theorem not_bodyEmpty_sliver :
    ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁) := by
  rintro hE
  obtain ⟨X, hX⟩ := QMCLeafB.AnchorFactsM2.realBody_G₁
  exact hE X hX

#print axioms QMCLeafB.TrueBitM5.not_bodyEmpty_sliver

/-- **`TripleSupply` is uninhabited at the campaign family, for every program bit.** -/
theorem not_tripleSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.ThriceM3.TripleSupply o QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  have hn : 2 ≤ QMCLeafB.AnchorFactsM2.G₁.n := QMCLeafB.AnchorFactsM2.hn₁
  have hlo : -QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ ≤ QMCLeafB.AnchorFactsM2.t₁ :=
    QMCLeafB.Audit2M5.anchor3_interior.1
  have hhi : (QMCLeafB.AnchorFactsM2.t₁ : ℝ)
      < -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 : ℚ)) : ℝ) :=
    QMCLeafB.Audit2M5.anchor3_interior.2
  by_cases hT : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true
  · exact QMCLeafB.AnchorFactsM2.not_coreDataG_G₁ o
      ⟨H.trueBit _ _ hn hlo hhi hT⟩
  · have hF : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = false := by
      cases hb : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ with
      | false => rfl
      | true => exact absurd hb hT
    have hRP : QMCLeafB.FinalStroke.RunParts o QMCLeafB.AnchorFactsM2.G₁
        QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.P₁ :=
      H.third _ _ hn hlo hhi not_bodyEmpty_sliver hF
    have htrue : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true :=
      QMCLeafB.BallM2.sliver_bit_true hRP
    rw [hF] at htrue
    exact Bool.noConfusion htrue

#print axioms QMCLeafB.TrueBitM5.not_tripleSupply

/-! ## 4.  The repaired split: the `true`-bit slot at the leaf's own interface

Three changes with respect to `Check_thrice_m3.TripleSupply`, each forced by §3:

* the `true`-bit slot is stated at `RunParts` (§1 produces it from one mint certificate), not at the
  conduit shape `CoreDataG`, whose `hmem` lives at the pinched diagonal and is therefore dead at every
  `¬ PinchFeasible` point — the sliver included;
* the empty-body branch no longer needs the campaign's `ok ⇒ pinched member` implication
  (`hokp`) nor the pinched-diagonal datum (`hdia`): its whole content is "the bit is `false` where
  the body is empty", one named design fact;
* the third stratum is unchanged — it is now the *only* analytic obligation, and §6 shows it is
  empty as soon as the design reads `true` at nonempty bodies.

The stroke below therefore has **no** hypothesis about the program's `ok` rounds at nonempty bodies.
That is the point: at the sliver the campaign's pinched `ok` test cannot report `ok`
(`OkProd_M8.oracleV_not_ok_at_G₁`), so any stroke carrying `hokp` at nonempty bodies is forced to
read the bit `false` there and then owes a `RunParts` the ball forbids (§3). -/

/-- **The `true`-bit slot, at `RunParts`.** -/
abbrev TrueBitParts (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = true → QMCLeafB.FinalStroke.RunParts o G t (Pfam G)

/-- **The repaired triple supply.**  Same two strata, `true`-bit slot at the leaf's interface. -/
structure TripleSupplyR (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type where
  /-- `RunParts` at the `true`-bit interior points (§1's mint route, or any other route) -/
  trueBitR : TrueBitParts o Pfam
  /-- `RunParts` at the `false`-bit points with a nonempty real body (the third stratum) -/
  third : QMCLeafB.ThriceM3.ThirdStratum o Pfam

/-- **The thrice-split production, repaired.**  Empty body ⇒ the bit is `false` (design fact) and
`RefutedM3.runParts_of_emptyBody` produces the record drift-free.  Nonempty body ⇒ split by the bit:
`true` is §1/`trueBitR`, `false` is the third stratum. -/
noncomputable def runParts_of_tripleR {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hbitFalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.ThriceM3.BodyEmpty G t (Pfam G) → o G t = false)
    (H : TripleSupplyR o Pfam) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (Pfam G) := by
  intro G t hn hlo hhi
  by_cases hbody : QMCLeafB.ThriceM3.BodyEmpty G t (Pfam G)
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t (Pfam G) hn
      (hbitFalse G t hbody) hbody
  · by_cases hT : o G t = true
    · exact H.trueBitR G t hn hlo hhi hT
    · refine H.third G t hn hlo hhi hbody ?_
      cases hb : o G t with
      | false => rfl
      | true => exact absurd hb hT

#print axioms QMCLeafB.TrueBitM5.runParts_of_tripleR

/-- **`HdProp` from the repaired supply.** -/
noncomputable def hdProp_of_tripleR
    (hbitFalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = false)
    (H : TripleSupplyR QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp :=
  fun G t hn hlo hhi => runParts_of_tripleR hbitFalse H G t hn hlo hhi

#print axioms QMCLeafB.TrueBitM5.hdProp_of_tripleR

/-- **`SolutionStatement` from the repaired supply.** -/
theorem solution_statement_of_tripleR
    (hbitFalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = false)
    (H : TripleSupplyR QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement (hdProp_of_tripleR hbitFalse H)

#print axioms QMCLeafB.TrueBitM5.solution_statement_of_tripleR

/-- **The verbatim `d9f601e5` sentence from the repaired supply.**  Compare
`Check_hemptyR_m3.solution_of_triple'`: one slot moved (`CoreDataG → RunParts`), and the campaign's
`rb`/`cXp`/`hbit`/`hokp`/`hdia` are all gone — the conclusion is written out literally, so this is
the statement lock. -/
theorem solution_of_tripleR
    (hbitFalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = false)
    (H : TripleSupplyR QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
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
  QMCLeafB.AssemblyM5.endgame_of_hd (hdProp_of_tripleR hbitFalse H)

#print axioms QMCLeafB.TrueBitM5.solution_of_tripleR

/-! ## 5.  Conservativity: the conduit lane is a special case

Nothing banked is lost: any `TripleSupply` producer (e.g. `Check_thrice_m3.tripleSupply_of_split`)
is a `TripleSupplyR` producer, because `CoreDataG` gives `RunParts`
(`Check_thrice_m3.runParts_of_coreDataG`).  The converse is where the gain lies (§2: the sliver). -/

/-- **`TripleSupply ⟹ TripleSupplyR`** at the campaign family (the conduit lane is wired to
`paramsKbc2` by construction). -/
noncomputable def tripleSupplyR_of_triple {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.ThriceM3.TripleSupply o QMCLeafB.UnionShallow.paramsKbc2) :
    TripleSupplyR o QMCLeafB.UnionShallow.paramsKbc2 where
  trueBitR := fun G t hn hlo hhi hT =>
    QMCLeafB.ThriceM3.runParts_of_coreDataG hlo hhi (H.trueBit G t hn hlo hhi hT)
  third := H.third

#print axioms QMCLeafB.TrueBitM5.tripleSupplyR_of_triple

/-! ## 6.  Empty by design: the exact condition, and the leaf from three design facts

The third stratum is a `∀` over `false`-bit nonempty-body points.  It is **empty by design** exactly
when the program's bit reads `true` at every nonempty-body interior point — then the third slot is
inhabited with no analytic work at all (`thirdStratum_of_design`).  With §1's mint route the whole
residual then reduces to:

* (`hbitFalse`) the bit is `false` where the real body is empty;
* (`hM`) the bit is `true` where the real body is nonempty — a statement about the program's own
  `ok` test and search;
* (`hcert`) a mint certificate exists at every nonempty body — the geometric statement the leaf's
  `4ε` mint budget (`OkLevelM5.campaign_engine_level_lt_mint`) is designed to buy.

No stratum, no drift, no pinch, no `hemptyR`. -/

/-- **The third stratum is vacuous as soon as the bit reads `true` at nonempty bodies.** -/
noncomputable def thirdStratum_of_design {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      ¬ QMCLeafB.ThriceM3.BodyEmpty G t (Pfam G) → o G t = true) :
    QMCLeafB.ThriceM3.ThirdStratum o Pfam := by
  intro G t hn hlo hhi hbody hF
  exact absurd (hM G t hbody) (by rw [hF]; simp)

#print axioms QMCLeafB.TrueBitM5.thirdStratum_of_design

/-- **The repaired supply, from the design facts alone.**  `hbitFalse` is the empty side (the bit is
`false` wherever the real body is empty), `hM` the nonempty side (the program's `ok` test fires), and
`hcert` the mint certificate the leaf's `4ε` budget buys.  Then both slots are filled with no analytic
obligation left: the `true` slot by §1, the third stratum **vacuously** (`hM` denies its hypothesis). -/
noncomputable def tripleSupplyR_of_design
    (hbitFalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = false)
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ¬ QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = true)
    (hcert : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ¬ QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      MintCert G t) :
    TripleSupplyR QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2 where
  trueBitR := by
    intro G t _hn hlo hhi hT
    by_cases hbody : QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G)
    · rw [hbitFalse G t hbody] at hT
      exact absurd hT (by simp)
    · exact runParts_of_mintCert (one_le_km G) hT (hcert G t hlo hhi hbody)
  third := by
    intro G t _hn hlo hhi hbody hF
    exact absurd (hM G t hlo hhi hbody) (by rw [hF]; simp)

#print axioms QMCLeafB.TrueBitM5.tripleSupplyR_of_design

/-- **The leaf's residual from the three design facts, with no stratum at all.**  This is the
machine-checked form of "the third stratum is empty by design": `ResidParts` is produced without ever
asking a `false`-bit nonempty-body point for anything. -/
noncomputable def residParts_of_design
    (hbitFalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = false)
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ¬ QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = true)
    (hcert : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ¬ QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      MintCert G t) :
    QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2 := by
  intro G t _hn hlo hhi _hbody
  by_cases hbody : QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G)
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) _hn (hbitFalse G t hbody) hbody
  · exact runParts_of_mintCert (one_le_km G) (hM G t hlo hhi hbody)
      (hcert G t hlo hhi hbody)

#print axioms QMCLeafB.TrueBitM5.residParts_of_design

/-- **The verbatim `d9f601e5` sentence from the three design facts.** -/
theorem solution_of_design
    (hbitFalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = false)
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ¬ QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = true)
    (hcert : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ¬ QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      MintCert G t) :
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
  solution_of_tripleR hbitFalse (tripleSupplyR_of_design hbitFalse hM hcert)

#print axioms QMCLeafB.TrueBitM5.solution_of_design

/-- **Statement lock**: the verbatim conclusion written out in `solution_of_tripleR` is the shelf's
own `SolutionStatement` — the ascription below only elaborates if the two are definitionally the
same type. -/
theorem solution_of_tripleR_is_statement
    (hbitFalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.Audit2M5.campaignBit G t = false)
    (H : TripleSupplyR QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_tripleR hbitFalse H

#print axioms QMCLeafB.TrueBitM5.solution_of_tripleR_is_statement

/-- **The sliver is a `true`-bit point of the repaired supply**: the true-bit slot's conclusion is
inhabited there (`runParts_sliver_trueBit`), while the conduit slot of `TripleSupply` is dead there
(`AnchorFactsM2.not_coreDataG_G₁`).  So the repaired slot is strictly weaker — it is inhabited
exactly where the old one is not. -/
theorem sliver_trueBitR_inhabited :
    Nonempty (QMCLeafB.FinalStroke.RunParts (fun _ _ => true) QMCLeafB.AnchorFactsM2.G₁
      QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.P₁) ∧
    ¬ Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) QMCLeafB.AnchorFactsM2.G₁
      QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.P₁ QMCLeafB.AnchorFactsM2.hn₁) :=
  ⟨⟨runParts_sliver_trueBit⟩, QMCLeafB.AnchorFactsM2.not_coreDataG_G₁ _⟩

#print axioms QMCLeafB.TrueBitM5.sliver_trueBitR_inhabited

end QMCLeafB.TrueBitM5


