-- Prove2me | Definitions.Def_QMCLeafB_traj_m3
-- name    : QMCLeafB_traj_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:29:11.180522+00:00
-- url     : https://prove2.me/theorems/bcd4bbda-f6b1-4ac0-970e-56a7476e9ceb
-- title:
--   QMCLeafB traj_m3
-- statement:
--   # `Check_traj_m3` — phase 26, member m3, direction `trajectory-ball-true`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_dichot
import Definitions.Def_QMCLeafB_audit25
/-
# `Check_traj_m3` — phase 26, member m3, direction `trajectory-ball-true`

**The object.**  A `FinalStroke.RunParts` records the *verdicts* of a run — the `ok`/`cut` flags, the
recorded cut data, the ledger — but **not** the centres that were queried.  Every statement about
"the descent reached the body" therefore has to re-introduce the centres.  This file adds that
object:

```lean
structure TestRun (o) (G) (t) (P) where
  toParts : RunParts o G t P
  cX      : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  htest   : ∀ k, (toParts.ok k = true ↔ RelaxMem (wMatrixQ G) (cX k) (t - eps G) P.dq)
```

`htest` is the level coherence the campaign's program owes: the `ok` flag of a round **is** the
feasibility test at that round's own centre, at the engine's level `t − ε` and tolerance `dq`.
Nothing is assumed about the centres' shape — in particular nothing about their diagonal.

**What is proved.**

* **§2 THE VISIT THEOREM.**  At a body carrying the campaign's ball `dq/(8(c_A+1))`, *every*
  test-run has a centre that is a member below the horizon (`exists_member_of_ball`):
  `∃ k < K·m, RelaxMem (wMatrixQ G) (cX k) (t − ε) dq`.  The volume obstruction
  (`BallM2.no_runParts_of_ball`) forbids an all-`cut` stream; `htest` turns that into a
  *reachability* statement about the centres — the precise form of "the descent forces the centre
  into the body within `K·m` rounds", at an explicitly bounded round index.
* **§3 THE PINCH IS IMPOSSIBLE, for every bit and every record.**  The sliver carries the campaign's
  own ball (`BallM2.sliver_ball_campaign`), so a test-run there must *visit* a member; but no matrix
  with diagonal pinned to `1 − dq/4` is a member (`EmptyBodyM5.no_pinched_member_G₁`).  Hence
  **there is no `TestRun` at the sliver whose centres are pinned** (`not_pinned_testRun`) — with no
  read-out hypothesis at all, unlike `DichotM3.sliver_no_runParts_of_pinched_readout`.  The stratum
  form (`not_pinned_of_no_pinched_member`) is the same at any ball-bearing body.  Design receipt: the
  frozen `cXst` normalisation cannot be the query sequence of a correct descent.
* **§4 NON-VACUITY.**  `sliver_testRun` is a `TestRun` at the sliver with constant-`true` stream and
  centres the rational member `Q₁ = !![1,s;s,1]` (`EmptyBodyM5.body_nonempty_G₁`).  So §3 excludes a
  real object.
* **§5 LEVEL COHERENCE.**  The engine's accept level `t − ε + dq/2` sits strictly below the leaf's
  mint `t + ε` at the sliver (`sliver_level_lt_mint`), so an accepted centre never overshoots the
  leaf's tolerance (`member_frob_le_mint`); the pinch floor `1 − dq/4` misses the member threshold
  `1 − dq/8` by exactly `dq/8` (`pinch_short_by`).
* **§6 THE REMAINDER, NAMED.**  A *family* of test-runs supplies exactly `Package`'s two datum slots
  `hbit`/`hok` (`testRunFamily_slots`): the `ok`-stream read-out is not extra structure, and the only
  slot of `Package` that is not a test-run family is `parts : ResidParts campaignBit paramsKbc2`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom receipts at the end (expected `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.TrajM3

open QuantumMaxCutEnergy

/-! ## 0.  The sliver's names, local -/

/-- The sliver input (`= Check_anchorfacts_m2.G₁`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.AnchorFactsM2.G₁

/-- The sliver threshold (`= Check_anchorfacts_m2.t₁`). -/
abbrev t₁ : ℚ := QMCLeafB.AnchorFactsM2.t₁

/-- The campaign parameter family at `G₁`. -/
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.UnionShallow.paramsKbc2 G₁

theorem hn₁ : 2 ≤ G₁.n := QMCLeafB.AnchorFactsM2.hn₁

/-! ## 1.  The test-run -/

/-- **A run together with its query centres.**  `htest` is the level coherence: `ok k` holds exactly
when round `k`'s centre passes the engine's membership test `RelaxMem … (t − ε) dq`. -/
structure TestRun (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) where
  /-- the run's record (verdicts, cuts, ledger) -/
  toParts : QMCLeafB.FinalStroke.RunParts o G t P
  /-- the centres the run queried -/
  cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  /-- the `ok` flag is the test at the centre, at the engine's own level -/
  htest : ∀ k,
    (toParts.ok k = true ↔
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)

namespace TestRun

variable {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
variable {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}

/-- **The bit is exactly "the descent visited a member below the horizon".** -/
theorem bit_true_iff_exists_member (T : TestRun o G t P) :
    o G t = true ↔ ∃ k, k < P.K * P.m ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (T.cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq := by
  rw [T.toParts.hverdict,
    QMCLeafB.SimLoop.anyOk_eq_true_iff (T.toParts.ok) (P.K * P.m)]
  constructor
  · rintro ⟨k, hk, hok⟩
    exact ⟨k, hk, (T.htest k).mp hok⟩
  · rintro ⟨k, hk, hm⟩
    exact ⟨k, hk, (T.htest k).mpr hm⟩

/-- A `true` bit names a round whose centre is a member. -/
theorem exists_member_of_bit_true (T : TestRun o G t P) (h : o G t = true) :
    ∃ k, k < P.K * P.m ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (T.cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq :=
  T.bit_true_iff_exists_member.mp h

/-- A `false` bit says every queried centre below the horizon fails the test. -/
theorem not_member_of_bit_false (T : TestRun o G t P) (h : o G t = false) :
    ∀ k, k < P.K * P.m →
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (T.cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq := by
  intro k hk hm
  have htrue : o G t = true := T.bit_true_iff_exists_member.mpr ⟨k, hk, hm⟩
  rw [h] at htrue
  exact Bool.noConfusion htrue

/-- **The test's forward direction is the read-out slot**: an `ok` round names a member centre. -/
theorem member_of_ok (T : TestRun o G t P) {k : ℕ} (hok : T.toParts.ok k = true) :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (T.cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq :=
  (T.htest k).mp hok

end TestRun

/-! ## 2.  THE VISIT THEOREM -/

/-- **THE VISIT THEOREM.**  At a body carrying the campaign ball `dq/(8(c_A+1))`, every test-run
visits a member below the horizon. -/
theorem exists_member_of_ball {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (T : TestRun o G t P) (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P) :
    ∃ k, k < P.K * P.m ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (T.cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq :=
  T.exists_member_of_bit_true (QMCLeafB.BallM2.no_runParts_of_ball hn hball T.toParts)

/-! ## 3.  The pinch is impossible wherever the ball sits -/

/-- **NO PINNED TEST-RUN AT THE SLIVER.** -/
theorem not_pinned_testRun (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (T : TestRun o G₁ t₁ P₁)
    (hpin : ∀ k (i : Fin G₁.n), T.cX k i i = 1 - P₁.dq / 4) : False := by
  obtain ⟨k, _hk, hM⟩ :=
    exists_member_of_ball (T := T) hn₁ QMCLeafB.BallM2.sliver_ball_campaign
  exact QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ (T.cX k) (fun i => hpin k i) hM

/-- **The stratum form.** -/
theorem not_pinned_of_no_pinched_member {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (T : TestRun o G t P) (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P)
    (hnopinch : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ, (∀ i, Q i i = 1 - P.dq / 4) →
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hpin : ∀ k (i : Fin G.n), T.cX k i i = 1 - P.dq / 4) : False := by
  obtain ⟨k, _hk, hM⟩ := exists_member_of_ball (T := T) hn hball
  exact hnopinch (T.cX k) (fun i => hpin k i) hM

/-- **The `ok` lane's centre is never pinned.** -/
theorem ok_centre_not_pinned (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (T : TestRun o G₁ t₁ P₁) {k : ℕ} (hok : T.toParts.ok k = true) :
    ¬ (∀ i : Fin G₁.n, T.cX k i i = 1 - P₁.dq / 4) := by
  intro hpin
  exact QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ (T.cX k) hpin (T.member_of_ok hok)

/-! ## 4.  Non-vacuity: the un-pinned lane is inhabited at the sliver -/

/-- **A test-run at the sliver with un-pinned centres.** -/
def sliver_testRun : TestRun (fun _ _ => true) G₁ t₁ P₁ where
  toParts := QMCLeafB.DichotM3.sliver_runParts
  cX := fun _ => QMCLeafB.EmptyBodyM5.Q₁
  htest := by
    intro k
    exact ⟨fun _ => QMCLeafB.EmptyBodyM5.body_nonempty_G₁, fun _ => rfl⟩

theorem sliver_testRun_bit : (fun _ _ => true : QuantumMaxCutEnergy.Input → ℚ → Bool) G₁ t₁
    = true := rfl

/-- The un-pinned test-run is not pinned: `1 − dq/4 < 1`. -/
theorem sliver_testRun_unpinned (k : ℕ) :
    ¬ (∀ i : Fin G₁.n, sliver_testRun.cX k i i = 1 - P₁.dq / 4) := by
  intro h
  have h0 := h 0
  have h1 : sliver_testRun.cX k 0 0 = 1 := rfl
  have hdq : (0 : ℚ) < P₁.dq := P₁.hdq
  rw [h1] at h0
  linarith

/-- **Every test-run at the sliver reads `true`** (the ball decides the bit). -/
theorem testRun_bit_true_at_sliver (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (T : TestRun o G₁ t₁ P₁) : o G₁ t₁ = true :=
  QMCLeafB.BallM2.sliver_bit_true T.toParts

/-- **Every test-run at the sliver visits a member below the horizon.** -/
theorem sliver_visit (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (T : TestRun o G₁ t₁ P₁) :
    ∃ k, k < P₁.K * P₁.m ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) (T.cX k)
        (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq :=
  exists_member_of_ball (T := T) hn₁ QMCLeafB.BallM2.sliver_ball_campaign

/-! ## 5.  Level coherence and the `dq/8` gap -/

/-- **The engine's accept level is strictly below the leaf's mint level at the sliver.** -/
theorem sliver_level_lt_mint :
    t₁ - QMCLeafB.RundataCert.eps G₁ + P₁.dq / 2
      < t₁ + QMCLeafB.RundataCert.eps G₁ := by
  have heps : QMCLeafB.RundataCert.eps G₁ = 1 / 20000 := QMCLeafB.EmptyBodyM5.eps_G₁
  have hdq : P₁.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq
  have ht : t₁ = -(2 : ℚ) + 71 / 1520000 := rfl
  rw [heps, hdq, ht]
  norm_num

/-- **Coherence, generic form**: a member at the engine's level is below the leaf's mint level
whenever `dq/2 ≤ 2ε`. -/
theorem member_frob_le_mint {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {Q : Matrix (Fin G.n) (Fin G.n) ℚ}
    (hM : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
      (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hlev : t - QMCLeafB.RundataCert.eps G + P.dq / 2
      ≤ t + QMCLeafB.EngineRuntime.Rq G / 40000) :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) Q
      ≤ t + QMCLeafB.EngineRuntime.Rq G / 40000 := by
  have h := hM.trace_le
  linarith

/-- **The pinch is short of the member threshold by exactly `dq/8`.** -/
theorem pinch_short_by : 1 - P₁.dq / 8 - (1 - P₁.dq / 4) = P₁.dq / 8 :=
  QMCLeafB.DichotM3.pinch_gap

/-- The pinned diagonal is strictly below the member threshold. -/
theorem pinched_diag_not_member_level :
    ¬ (1 - P₁.dq / 8 ≤ 1 - P₁.dq / 4) :=
  QMCLeafB.DichotM3.pinch_edge_excluded

/-! ## 6.  The remainder, named -/

/-- **A test-run family supplies `Package`'s datum slots.** -/
theorem testRunFamily_slots
    (Ts : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      TestRun (QMCLeafB.Audit2M5.campaignBit) G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
        QMCLeafB.Audit2M5.campaignBit G t
          = QMCLeafB.SimLoop.anyOk (fun k => (Ts G t).toParts.ok k)
              ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
      ∧ (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ),
          (Ts G t).toParts.ok k = true →
            QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) ((Ts G t).cX k)
              (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq) := by
  refine ⟨fun G t => (Ts G t).toParts.hverdict, ?_⟩
  intro G t k hok
  exact (Ts G t).member_of_ok hok

end QMCLeafB.TrajM3

/-! ## 7.  Axiom receipts -/

#print axioms QMCLeafB.TrajM3.hn₁
#print axioms QMCLeafB.TrajM3.TestRun.bit_true_iff_exists_member
#print axioms QMCLeafB.TrajM3.TestRun.exists_member_of_bit_true
#print axioms QMCLeafB.TrajM3.TestRun.not_member_of_bit_false
#print axioms QMCLeafB.TrajM3.TestRun.member_of_ok
#print axioms QMCLeafB.TrajM3.exists_member_of_ball
#print axioms QMCLeafB.TrajM3.not_pinned_testRun
#print axioms QMCLeafB.TrajM3.not_pinned_of_no_pinched_member
#print axioms QMCLeafB.TrajM3.ok_centre_not_pinned
#print axioms QMCLeafB.TrajM3.sliver_testRun
#print axioms QMCLeafB.TrajM3.sliver_testRun_bit
#print axioms QMCLeafB.TrajM3.sliver_testRun_unpinned
#print axioms QMCLeafB.TrajM3.testRun_bit_true_at_sliver
#print axioms QMCLeafB.TrajM3.sliver_visit
#print axioms QMCLeafB.TrajM3.sliver_level_lt_mint
#print axioms QMCLeafB.TrajM3.member_frob_le_mint
#print axioms QMCLeafB.TrajM3.pinch_short_by
#print axioms QMCLeafB.TrajM3.pinched_diag_not_member_level
#print axioms QMCLeafB.TrajM3.testRunFamily_slots

namespace QMCLeafB.TrajM3

/-! ## 7.  The package, from a test-run family — the remainder in closed form

`Audit25M8.Package`'s two datum slots are exactly a test-run family's data (§6), and its third slot
`parts : ResidParts campaignBit paramsKbc2` is supplied by the very same family: at every interior
nonempty-body point the family's own record *is* the `RunParts` the residual asks for.  So the whole
leaf reduces to one statement about the program:

> at every `(G,t)`, the program's `ok` flag is the level test at its own centre.

That is `Nonempty Package`, hence (by the banked verbatim stroke) `d9f601e5`.  The clean
contrapositive is §7c: a family with **pinned** centres does not exist at the sliver. -/

/-- **`Package` FROM A TEST-RUN FAMILY.**  The three slots: `hbit` is the run's verdict equation,
`hok` is the test's forward direction at the queried centre, `parts` is the family's own record. -/
theorem package_of_testRunFamily
    (Ts : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      TestRun (QMCLeafB.Audit2M5.campaignBit) G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    Nonempty QMCLeafB.Audit25M8.Package :=
  ⟨{ rb := fun G t k => (Ts G t).toParts.ok k
     cXp := fun G t k => (Ts G t).cX k
     hbit := fun G t => (Ts G t).toParts.hverdict
     hok := fun G t k hk => (Ts G t).member_of_ok hk
     parts := fun G t _hn _hlo _hhi _hbody => (Ts G t).toParts }⟩

/-- **The verbatim `d9f601e5` sentence** from a test-run family at the campaign's bit. -/
theorem solution_of_testRunFamily
    (Ts : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      TestRun (QMCLeafB.Audit2M5.campaignBit) G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.Audit25M8.Target := by
  obtain ⟨P⟩ := package_of_testRunFamily Ts
  exact QMCLeafB.Audit25M8.solution_of_package P

/-- **7c. A pinned family does not exist.**  At the sliver the campaign's ball forces an `ok` round,
whose centre is then a member; pinned centres are never members.  So no test-run family — hence no
`Package` — has the frozen `cXst` normalisation as its query sequence. -/
theorem not_pinned_testRunFamily
    (Ts : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      TestRun (QMCLeafB.Audit2M5.campaignBit) G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hpin : ∀ k (i : Fin G₁.n), (Ts G₁ t₁).cX k i i = 1 - P₁.dq / 4) : False :=
  not_pinned_testRun _ (Ts G₁ t₁) hpin

/-- **A pinned family of the concrete run is refuted** in the library's own normalisation
(`RecordsM2.cXst` has diagonal `1 − dq/4` by definition, `DichotM3.cXst_hdia`): if the campaign's
query centres are `cXst`, then there is no test-run family at all. -/
theorem no_testRunFamily_at_pinned_centres
    (Ts : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      TestRun (QMCLeafB.Audit2M5.campaignBit) G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hpin : ∀ k (i : Fin G₁.n),
      (Ts G₁ t₁).cX k i i
        = QMCLeafB.RecordsM2.cXst G₁.n (fun _ => ([] : List ℚ)) P₁.dq k i i) : False := by
  refine not_pinned_testRunFamily Ts ?_
  intro k i
  rw [hpin k i, QMCLeafB.DichotM3.cXst_hdia]

/-- **The bit is not free.**  Every test-run family at the campaign's bit has
`campaignBit G₁ t₁ = true`, so a program whose centres are pinned there is not merely excluded
(§7c) but excluded *by its own bit*. -/
theorem testRunFamily_bit_at_sliver
    (Ts : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      TestRun (QMCLeafB.Audit2M5.campaignBit) G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.Audit2M5.campaignBit G₁ t₁ = true :=
  testRun_bit_true_at_sliver _ (Ts G₁ t₁)

end QMCLeafB.TrajM3

#print axioms QMCLeafB.TrajM3.package_of_testRunFamily
#print axioms QMCLeafB.TrajM3.solution_of_testRunFamily
#print axioms QMCLeafB.TrajM3.not_pinned_testRunFamily
#print axioms QMCLeafB.TrajM3.no_testRunFamily_at_pinned_centres
#print axioms QMCLeafB.TrajM3.testRunFamily_bit_at_sliver

namespace QMCLeafB.TrajM3

/-! ## 8.  The sliver's obligation is exactly one Boolean

At `(G₁,t₁)` the residual `RunParts campaignBit G₁ t₁ P₁` exists **iff** the campaign's bit reads
`true` there:

* `→` is the volume obstruction (`BallM2.sliver_bit_true`);
* `←` is `DichotM3.sliver_runParts` — the constant-`true` `ok` stream with the un-pinned member
  centre and the banked leaf-level certificate — transported to the campaign's bit.

So the sliver contributes *no* content to the residual beyond the bit equation.  And the other two
slots of `Package` are satisfiable there for either bit (`datum_slots_satisfiable_at_sliver`), so the
sliver is not the obstruction of the package *shape* either: what remains is the off-sliver residual
plus the bit equation at the sliver. -/

theorem anyOk_false_stream : ∀ T : ℕ,
    QMCLeafB.SimLoop.anyOk (fun _ => false) T = false
  | 0 => rfl
  | (k + 1) => by
      rw [QMCLeafB.SimLoop.anyOk_succ, anyOk_false_stream k]
      rfl

/-- **`←` of the iff**: a `true` bit at the sliver gives the residual's record there. -/
def runParts_of_bit_true_at_sliver
    (hbit : QMCLeafB.Audit2M5.campaignBit G₁ t₁ = true) :
    QMCLeafB.FinalStroke.RunParts QMCLeafB.Audit2M5.campaignBit G₁ t₁ P₁ where
  ok := fun _ => true
  cd := fun _ => ⟨0, 0, 0⟩
  del := fun _ => 0
  hcert := fun _ _ _ => QMCLeafB.BallM2.sliver_hcert_witness
  hwit := fun _ _ h => Bool.noConfusion h
  hrho := fun _ _ h => Bool.noConfusion h
  hcne := fun _ _ h => Bool.noConfusion h
  hdel0 := fun _ _ h => Bool.noConfusion h
  hcheck := fun _ _ h => Bool.noConfusion h
  hle := fun _ _ h => Bool.noConfusion h
  hcut := fun _ _ h => Bool.noConfusion h
  hverdict := by
    have hpos : 0 < P₁.K * P₁.m :=
      Nat.lt_trans (by norm_num) QMCLeafB.AnchorFactsM2.Km₁
    exact hbit.trans (QMCLeafB.DichotM3.anyOk_true_of_pos _ hpos).symm

/-- **THE SLIVER'S OBLIGATION IS ONE BOOLEAN.**  `RunParts` at the sliver exists iff the campaign's
bit reads `true`. -/
theorem residParts_at_sliver_iff :
    Nonempty (QMCLeafB.FinalStroke.RunParts QMCLeafB.Audit2M5.campaignBit G₁ t₁ P₁)
      ↔ QMCLeafB.Audit2M5.campaignBit G₁ t₁ = true := by
  constructor
  · rintro ⟨B⟩
    exact QMCLeafB.BallM2.sliver_bit_true B
  · intro h
    exact ⟨runParts_of_bit_true_at_sliver h⟩

/-- **The two read-out slots are satisfiable at the sliver for either bit.**  `Package`'s
`hbit`/`hok` obstruct nothing at `(G₁,t₁)`: with the bit `true` take the constant-`true` stream and
the un-pinned member `Q₁` at every round; with the bit `false` the constant-`false` stream, where
`hok` is vacuous. -/
theorem datum_slots_satisfiable_at_sliver :
    ∃ (rb : ℕ → Bool) (cXp : ℕ → Matrix (Fin G₁.n) (Fin G₁.n) ℚ),
      QMCLeafB.Audit2M5.campaignBit G₁ t₁
          = QMCLeafB.SimLoop.anyOk rb (P₁.K * P₁.m)
        ∧ (∀ k, rb k = true →
            QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) (cXp k)
              (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq) := by
  have hpos : 0 < P₁.K * P₁.m :=
    Nat.lt_trans (by norm_num) QMCLeafB.AnchorFactsM2.Km₁
  cases hb : QMCLeafB.Audit2M5.campaignBit G₁ t₁ with
  | true =>
      refine ⟨fun _ => true, fun _ => QMCLeafB.EmptyBodyM5.Q₁, ?_, ?_⟩
      · rw [QMCLeafB.DichotM3.anyOk_true_of_pos _ hpos]
      · intro k _
        exact QMCLeafB.EmptyBodyM5.body_nonempty_G₁
  | false =>
      refine ⟨fun _ => false, fun _ => QMCLeafB.EmptyBodyM5.Q₁, ?_, ?_⟩
      · rw [anyOk_false_stream]
      · intro k hk
        exact Bool.noConfusion hk

/-- **The residual off the sliver, patched at it.**  If the campaign's bit reads `true` at the
sliver and the residual holds at every *other* interior nonempty-body point, the whole residual
holds.  So the sliver is free once the bit equation is known. -/
def residParts_of_off_sliver
    (hbit : QMCLeafB.Audit2M5.campaignBit G₁ t₁ = true)
    (Hoff : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ¬ (G = G₁ ∧ t = t₁) →
      QMCLeafB.FinalStroke.RunParts QMCLeafB.Audit2M5.campaignBit G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2 := by
  intro G t hn hlo hhi hbody
  by_cases h : G = G₁ ∧ t = t₁
  · obtain ⟨rfl, rfl⟩ := h
    exact runParts_of_bit_true_at_sliver hbit
  · exact Hoff G t hn hlo hhi hbody h

end QMCLeafB.TrajM3

#print axioms QMCLeafB.TrajM3.anyOk_false_stream
#print axioms QMCLeafB.TrajM3.runParts_of_bit_true_at_sliver
#print axioms QMCLeafB.TrajM3.residParts_at_sliver_iff
#print axioms QMCLeafB.TrajM3.datum_slots_satisfiable_at_sliver
#print axioms QMCLeafB.TrajM3.residParts_of_off_sliver

namespace QMCLeafB.TrajM3

/-! ## 9.  Two consequences: a `false` bit is ball-free, and the package stroke with the sliver removed -/

/-- **A `false` bit is ball-free.**  A test-run reading `false` at an interior point with a nonempty
body cannot have the campaign's ball in its body: the visit theorem would force an `ok` round.  (The
test-level twin of `TruebitG_M5.falseBit_ballFree`; no read-out data enters.) -/
theorem false_bit_ball_free {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (T : TestRun o G t P) (hn : 2 ≤ G.n) (hfalse : o G t = false)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} :
    ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P) := by
  intro hball
  have htrue : o G t = true := QMCLeafB.BallM2.no_runParts_of_ball hn hball T.toParts
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

/-- **THE PACKAGE STROKE WITH THE SLIVER REMOVED.**  `Package`'s three slots split as: the global
read-out datum (`hbit`, `hok`), the residual **off** the sliver, and the single Boolean
`campaignBit G₁ t₁ = true` — which is exactly the sliver's residual, by §8's iff
(`residParts_at_sliver_iff`).  So no `RunParts` construction is owed at the sliver beyond the bit. -/
theorem package_of_off_sliver
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbitR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hbit : QMCLeafB.Audit2M5.campaignBit G₁ t₁ = true)
    (Hoff : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ¬ (G = G₁ ∧ t = t₁) →
      QMCLeafB.FinalStroke.RunParts QMCLeafB.Audit2M5.campaignBit G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    Nonempty QMCLeafB.Audit25M8.Package :=
  ⟨{ rb := rb, cXp := cXp, hbit := hbitR, hok := hokR
     parts := residParts_of_off_sliver hbit Hoff }⟩

end QMCLeafB.TrajM3

#print axioms QMCLeafB.TrajM3.false_bit_ball_free
#print axioms QMCLeafB.TrajM3.package_of_off_sliver

namespace QMCLeafB.TrajM3

/-! ## 10.  The fifth vacuity, at the `Package` level

`Package` is *empty* once its datum slots are the campaign's own: the run queries the frozen
`cXst` centres, whose diagonal is `1 − dq/4`; no such matrix is a member at the sliver, so the
run's flags are all `false` below the horizon and the bit reads `false` there
(`ThriceM3.bit_false_at_exemplar`).  But `Package.parts` forces the bit `true` at the sliver
(`BallM2.sliver_bit_true`).  So:

* `Package` with the campaign's read-out data is **uninhabited** — the round's centre normalisation
  is the obstructive slot, not the residual;
* and the design repair is exactly §3's: the `ok` round's centre must be un-pinned.

The kill is inherited from `DichotM3.not_residParts_of_data` and lifted to `Package` here. -/

/-- **THE FIFTH VACUITY AT THE `PACKAGE` LEVEL.**  `Package` plus the campaign's pinched read-out
data (`hbit`/`hok`/`hdia`) is contradictory. -/
theorem package_empty_of_pinned_data
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) :
    ¬ Nonempty QMCLeafB.Audit25M8.Package := by
  rintro ⟨P⟩
  exact QMCLeafB.DichotM3.not_residParts_of_data rb cXp hbit hok hdia ⟨P.parts⟩

/-- **The same, in `Package`-free form**: with the pinned read-out there is no `ResidParts` at the
campaign bit — the residual slot itself is dead. -/
theorem not_residParts_pinned_data
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) :
    ¬ Nonempty (QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :=
  QMCLeafB.DichotM3.not_residParts_of_data rb cXp hbit hok hdia

end QMCLeafB.TrajM3

#print axioms QMCLeafB.TrajM3.package_empty_of_pinned_data
#print axioms QMCLeafB.TrajM3.not_residParts_pinned_data


