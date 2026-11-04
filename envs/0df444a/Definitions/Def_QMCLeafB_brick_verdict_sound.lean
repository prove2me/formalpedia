-- Prove2me | Definitions.Def_QMCLeafB_brick_verdict_sound
-- name    : QMCLeafB_brick_verdict_sound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:21:16.395173+00:00
-- url     : https://prove2.me/theorems/eae8d174-11d3-43c9-84cd-b7e1cace361c
-- title:
--   QMCLeafB brick_verdict_sound
-- statement:
--   # leaf B phase 10 — brick `verdict-sound` (swarm `smw02tv7j`, member m8, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sim_loop_m6
import Definitions.Def_QMCLeafB_sim_poly_m4
/-
# leaf B phase 10 — brick `verdict-sound` (swarm `smw02tv7j`, member m8, direction d3)

The last hypothesis of the leaf is `QMCLeafB.FinishLine.SoundεOnBracket o`
(`Check_brick_finish_line` §6, consumed by `SimPoly.solution_of_loop`).  This file discharges it
from the **per-round data a fixed-round simulate produces**, and nothing else:

* §1 `SoundAt` — the two clauses of `SoundεOnBracket` at a *single* `(input, threshold)`, with the
  leaf's own slacks `εw = εr = Rq G / 40000`; `soundEpsOnBracket_iff` is the pointwise
  reformulation (`↔ ∀ G t, -Rq G ≤ t → t ≤ 0 → SoundAt o G t`).  This is the shape every other
  brick should aim at; `SoundεOnBracket` itself is only the `∀`-closure of it.
* §2 **the top of the bracket is free.**  For `t ≥ -εr` the identity is a feasible witness
  (`tr (wMatrix G · 1) = 0`), so *any* verdict that says `true` there is feasible-sound with no
  computation at all (`exists_trace_le_of_neg_eps_le`).  A run therefore only has to be produced
  on `[-Rq G, -εr)`; `soundEpsOnBracket_of_runData_interior` (§5) is the form that exploits it.
* §3 **below the floor the refutation is free.**  For `t ≤ -Rq G - εr` the floor
  `-Rq G ≤ tr (wMatrix G · Z)` (`FinishLine.neg_Rq_le_trace`) refutes, so again no computation is
  needed (`soundAt_false_of_le_floor`).  Together §2+§3 are the two "degenerate bracket endpoints"
  of the brief: the top slice is decided by the identity, the floor by `Rq`.
* §4 **degenerate orders** `G.n ≤ 1`: the graph has no edge, so `Rq G = 0` and `wMatrix G = 0`;
  every verdict is sound at every bracketed `t` (`soundAt_of_le_one`).  This case is *forced*: the
  engine's refutation chain needs `2 ≤ n`, and nothing in `QuantumMaxCutEnergy.Input` supplies it.
* §5 **the assembly.**  `RunData o G t` bundles exactly the hypotheses
  `SimLoop.simulate_refuted_sound` asks for (prefix-guarded, plus the feasible-round certificate and
  the verdict equation `o G t = anyOk ok (K·m)`); `soundAt_of_runData` turns one bundle into
  `SoundAt o G t`, and `soundEpsOnBracket_of_runData` / `_interior` close the bracket.
* §6 the fit check: `solution_of_loop_via_runData` feeds the result straight into
  `SimPoly.solution_of_loop`'s `hsound` slot and lands on `SolutionStatement` verbatim.

Nothing analytic is reproved here: §1-§5 are `Automatic.Poly`-free plumbing over
`Check_sim_loop_m6`'s soundness theorem and `Check_brick_finish_line`'s floor lemma.  No `sorry`,
no `axiom`; audit at the end.

## Interface contract (for `brick-sim-ground`)

Produce, for each `G` with `2 ≤ G.n` and each bracketed `t`, a term of
`QMCLeafB.VerdictSound.RunData o G t`.  Its fields are literally the hypothesis list of
`SimLoop.simulate_refuted_sound` (with the `ok k = false` guard on every prefix hypothesis) plus
`hcert` (the feasible round's witness at `εw = Rq G / 40000`) and `hverdict`.  Then
`QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData o hd` *is* `solution_of_loop`'s `hsound`.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.VerdictSound

open QuantumMaxCutEnergy

/-! ## 1.  The two clauses at one `(input, threshold)` -/

/-- **`SoundεOnBracket` at a single `(input, threshold)`**, with the leaf's own slacks.  The whole
brick works with this predicate; `soundEpsOnBracket_iff` says the closing form is its `∀`-closure
over the driver's bracket. -/
def SoundAt (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (G : QuantumMaxCutEnergy.Input)
    (t : ℚ) : Prop :=
  (o G t = true → ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)) ∧
  (o G t = false → ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD Z →
        (t : ℝ) - ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
          ≤ (QMCLeafB.wMatrix G * Z).trace)

/-- **The closing predicate is the bracket-restriction of `SoundAt`.**  Stated as an `↔` so that a
consumer can either split `SoundεOnBracket` into its two clauses or close it pointwise. -/
theorem soundEpsOnBracket_iff (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    QMCLeafB.FinishLine.SoundεOnBracket o ↔
      ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
        -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → SoundAt o G t := by
  constructor
  · rintro ⟨hfeas, href⟩ G t hlo hhi
    exact ⟨fun h => hfeas G t hlo hhi h, fun h => href G t hlo hhi h⟩
  · intro h
    exact ⟨fun G t hlo hhi ht => (h G t hlo hhi).1 ht,
      fun G t hlo hhi hf => (h G t hlo hhi).2 hf⟩

/-! ## 2.  The top of the bracket: the identity is a witness

`wMatrix G` has zero diagonal, so `tr (wMatrix G · 1) = 0` (`FinishLine.one_trace_eq_zero`).  Hence
whenever `-εr ≤ t` the identity already certifies the feasible branch.  Nothing about the run is
used — this removes a whole slice of the bracket from the simulate's obligations. -/

/-- The leaf's slack `εr = Rq G / 40000` is non-negative.  Used by every margin estimate below. -/
theorem eps_nonneg (G : QuantumMaxCutEnergy.Input) :
    (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
  have hRq : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.EngineRuntime.Rq_nonneg G
  have : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G / 40000 := by linarith
  exact_mod_cast this

/-- **Feasible witness on the top slice.**  For `t ≥ -εr` the identity is unit-diagonal
semidefinite with trace `0 ≤ t + εw`. -/
theorem exists_trace_le_of_neg_eps_le (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (ht : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
  refine ⟨1, QMCLeafB.AnswerProducer.isUnitDiagPSD_one, ?_⟩
  rw [QMCLeafB.FinishLine.one_trace_eq_zero]
  linarith

/-- The feasible clause of `SoundAt` is free at the top of the bracket. -/
theorem soundAt_true_of_neg_eps_le (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (_hbit : o G t = true)
    (ht : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) :=
  exists_trace_le_of_neg_eps_le G t ht

/-! ## 3.  Below the floor: the refutation is free

`-Rq G ≤ tr (wMatrix G · Z)` for every unit-diagonal PSD `Z` (`FinishLine.neg_Rq_le_trace`), so
below `-Rq G - εr` the `false` branch holds outright.  This is the "empty body" half of the audit's
endpoint analysis: past the floor there is nothing feasible to separate. -/

/-- **Refutation below the floor.**  For `t ≤ -Rq G - εr` the floor `-Rq G ≤ tr (wMatrix G · Z)`
gives the `false` clause directly. -/
theorem soundAt_false_of_le_floor (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (_hbit : o G t = false)
    (ht : (t : ℝ) ≤ -((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
      - ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)) :
    ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD Z →
        (t : ℝ) - ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
          ≤ (QMCLeafB.wMatrix G * Z).trace := by
  intro Z hZ
  have h := QMCLeafB.FinishLine.neg_Rq_le_trace G Z hZ
  have heps := eps_nonneg G
  linarith

/-- **The floor endpoint is decided for free too.**  At `t = -Rq G` the refuting branch holds from
the trace floor alone, because `-εr ≤ 0`.  So of the two bracket endpoints `t = 0` and `t = -Rq G`,
the top one is settled by the identity (§2) and the bottom one by `Rq`; a simulate only ever has to
run in the *open* interval. -/
theorem soundAt_false_at_floor (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) :
    o G (-(QMCLeafB.EngineRuntime.Rq G)) = false →
      ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD Z →
          ((-(QMCLeafB.EngineRuntime.Rq G) : ℚ) : ℝ)
              - ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
            ≤ (QMCLeafB.wMatrix G * Z).trace := by
  intro _ Z hZ
  have h := QMCLeafB.FinishLine.neg_Rq_le_trace G Z hZ
  have heps := eps_nonneg G
  have hcast : ((-(QMCLeafB.EngineRuntime.Rq G) : ℚ) : ℝ)
      = -((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by push_cast; ring
  rw [hcast]
  linarith

/-- **At `t = 0` the feasible branch is decided by the identity.**  `SoundεOnBracket`'s top
endpoint, in the form a consumer needs: no run, no witness search. -/
theorem exists_trace_le_zero (G : QuantumMaxCutEnergy.Input) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (0 : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
  have heps := eps_nonneg G
  simpa using exists_trace_le_of_neg_eps_le G 0 (by simpa using heps)

/-! ## 4.  Degenerate orders: `G.n ≤ 1`

`Edge n = {p : Fin n × Fin n // p.1 < p.2}` is empty for `n ≤ 1`, so the weight sum — hence
`Rq` — vanishes, and every entry of `wMatrix G` is a diagonal one, hence `0`.  Both clauses of
`SoundAt` then hold at every bracketed `t`, whatever the verdict bit is.  Nothing in
`QuantumMaxCutEnergy.Input` bounds `n` below, and the engine's refutation chain requires `2 ≤ n`,
so this case has to be closed separately — the simulate never runs here. -/

theorem edge_isEmpty_of_le_one {n : ℕ} (hn : n ≤ 1) : IsEmpty (QuantumMaxCutEnergy.Edge n) :=
  ⟨fun e => by
    obtain ⟨p, hp⟩ := e
    have h1 : p.1.val < 1 := lt_of_lt_of_le p.1.isLt hn
    have h2 : p.2.val < 1 := lt_of_lt_of_le p.2.isLt hn
    omega⟩

set_option linter.style.haveILetI false in
/-- The bracket has width zero for `n ≤ 1`: there is no edge, so `Rq = 0`. -/
theorem Rq_eq_zero_of_le_one {G : QuantumMaxCutEnergy.Input} (h : G.n ≤ 1) :
    QMCLeafB.EngineRuntime.Rq G = 0 := by
  haveI : IsEmpty (QuantumMaxCutEnergy.Edge G.n) := edge_isEmpty_of_le_one h
  unfold QMCLeafB.EngineRuntime.Rq
  rw [Finset.univ_eq_empty]
  simp

/-- For `n ≤ 1` the weight matrix is `0` (every index pair is a diagonal pair). -/
theorem wMatrix_eq_zero_of_le_one {G : QuantumMaxCutEnergy.Input} (h : G.n ≤ 1) :
    QMCLeafB.wMatrix G = 0 := by
  ext i j
  have hji : i = j := by
    apply Fin.ext
    have h1 : i.val < 1 := lt_of_lt_of_le i.isLt h
    have h2 : j.val < 1 := lt_of_lt_of_le j.isLt h
    omega
  subst hji
  rw [QMCLeafB.wMatrix_apply_of_eq]
  rfl

/-- Consequently the trace vanishes identically for `n ≤ 1`. -/
theorem trace_eq_zero_of_le_one {G : QuantumMaxCutEnergy.Input} (h : G.n ≤ 1)
    (Z : Matrix (Fin G.n) (Fin G.n) ℝ) :
    (QMCLeafB.wMatrix G * Z).trace = 0 := by
  rw [wMatrix_eq_zero_of_le_one h]
  simp

/-- **Every verdict is sound at a degenerate order.** -/
theorem soundAt_of_le_one (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    {G : QuantumMaxCutEnergy.Input} (h : G.n ≤ 1) (t : ℚ)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t) (hhi : t ≤ 0) : SoundAt o G t := by
  have hRq : QMCLeafB.EngineRuntime.Rq G = 0 := Rq_eq_zero_of_le_one h
  have h0 : (0 : ℚ) ≤ t := by
    rw [hRq] at hlo
    simpa using hlo
  have htop : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) := by
    rw [hRq, zero_div, Rat.cast_zero, neg_zero]
    exact_mod_cast h0
  constructor
  · intro _
    exact exists_trace_le_of_neg_eps_le G t htop
  · intro _ Z _
    rw [trace_eq_zero_of_le_one h Z, hRq, zero_div]
    simp only [Rat.cast_zero]
    have : (t : ℝ) ≤ 0 := by exact_mod_cast hhi
    linarith

/-! ## 5.  The assembly: one run bundle per `(input, threshold)`

`RunData` is the hypothesis list of `SimLoop.simulate_refuted_sound` verbatim (prefix-guarded, as a
fixed-round loop can supply it), together with the feasible round's certificate (`hcert`, at
`εw = Rq G / 40000`) and the verdict equation.  The two soundness theorems of
`Check_sim_loop_m6` then give the two clauses of `SoundAt` — the only mathematical input in the
file. -/

/-- **The output of a fixed-round simulate at one `(input, threshold)`.**  Fields 1-17 are exactly
`QMCLeafB.SimLoop.simulate_refuted_sound`'s hypotheses at `A = wMatrix G`, `εr = Rq G / 40000`;
`hcert` is `simulate_feasible_sound`'s hypothesis at the same `εw`; `hverdict` says the leaf's
verdict bit is the run's `anyOk`. -/
structure RunData (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (G : QuantumMaxCutEnergy.Input)
    (t : ℚ) : Type where
  /-- round count factor -/
  K : ℕ
  /-- halving time of the contraction factor -/
  m : ℕ
  /-- did round `k` report `ok`? -/
  ok : ℕ → Bool
  /-- the recorded cut sequence -/
  cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)
  /-- the oracle tolerance -/
  dq : ℚ
  /-- the ledger's `c_A ≥ ∑ᵢⱼ |Aᵢⱼ|` -/
  cAq : ℚ
  /-- the shallow regime's contraction ceiling -/
  rmax : ℚ
  /-- the per-round oracle margins -/
  del : ℕ → ℚ
  hdq : 0 < dq
  hcAq : 0 ≤ cAq
  hAsum : ∑ i, ∑ j, |QMCLeafB.wMatrix G i j| ≤ (cAq : ℝ)
  /-- the `ok` round hands over the primal point -/
  hcert : ∀ k, k < K * m → ok k = true →
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
  /-- every `cut` round recorded a genuine eigen-data witness -/
  hwit : ∀ k, k < K * m → ok k = false →
    QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2)) cd k *ᵥ (cd k).p
      = (cd k).c
  hrho : ∀ k, k < K * m → ok k = false → 0 ≤ (cd k).rho
  hcne : ∀ k, k < K * m → ok k = false → (cd k).c ≠ 0
  hdel0 : ∀ k, k < K * m → ok k = false → 0 ≤ del k
  hcheck : ∀ k, k < K * m → ok k = false →
    (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p
  /-- the oracle's contract: the recorded cut separates the whole relaxation -/
  hcut : ∀ k, k < K * m → ok k = false → ∀ z,
    z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (dq : ℝ)
        ((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ) →
      -(((del k : ℚ)) : ℝ)
        ≤ QMCLeafB.EngineIterates.cutCR cd k
            ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
              (0 : Fin (G.n * G.n) → ℝ) cd k)
  hrmax : 0 ≤ rmax
  hle : ∀ k, k < K * m → ok k = false → (cd k).rho ≤ rmax
  hhalve : (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2
  hbudget : QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2)) * (1 / 2) ^ K
    < ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (G.n * G.n)
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (K * m)

/-- **One run is sound.**  The feasible branch is `simulate_feasible_sound`, the refuted branch
`simulate_refuted_sound`; the `AnswerProducer`/`ModernConvex` spellings of `IsUnitDiagPSD` are the
same term. -/
theorem soundAt_of_runData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
    (d : RunData o G t) : SoundAt o G t := by
  constructor
  · intro hbit
    have hv : QMCLeafB.SimLoop.anyOk d.ok (d.K * d.m) = true := by
      rw [← d.hverdict]
      exact hbit
    exact QMCLeafB.SimLoop.simulate_feasible_sound
      (A := QMCLeafB.wMatrix G) (t := t)
      (εw := QMCLeafB.EngineRuntime.Rq G / 40000) (T := d.K * d.m) d.hcert hv
  · intro hbit
    have hv : QMCLeafB.SimLoop.anyOk d.ok (d.K * d.m) = false := by
      rw [← d.hverdict]
      exact hbit
    intro Z hZ
    exact QMCLeafB.SimLoop.simulate_refuted_sound (n := G.n) (hn := hn)
      (A := QMCLeafB.wMatrix G) (t := t) (εr := QMCLeafB.EngineRuntime.Rq G / 40000)
      (δq := d.dq) (cAq := d.cAq) (hδq := d.hdq) (hcAq := d.hcAq) (hAsum := d.hAsum)
      (ok := d.ok) (m := d.m) (K := d.K) (cd := d.cd)
      (hwit := d.hwit) (hρ := d.hrho) (hcne := d.hcne) (δ := d.del)
      (hδ0 := d.hdel0) (hcheck := d.hcheck) (hcutδ := d.hcut)
      (ρmax := d.rmax) (hρmax := d.hrmax) (hle := d.hle) (hm := d.hhalve)
      (hK := d.hbudget) (hv := hv) Z hZ

/-- **The deliverable.**  A run bundle for every input of order at least two and every bracketed
threshold yields `SoundεOnBracket o`, which is `SimPoly.solution_of_loop`'s `hsound` slot
verbatim. -/
theorem soundEpsOnBracket_of_runData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → RunData o G t) :
    QMCLeafB.FinishLine.SoundεOnBracket o := by
  rw [soundEpsOnBracket_iff o]
  intro G t hlo hhi
  by_cases h : G.n ≤ 1
  · exact soundAt_of_le_one o h t hlo hhi
  · exact soundAt_of_runData o G t (by omega) (hd G t (by omega) hlo hhi)

/-- **The form that uses the free top slice.**  The simulate is only needed on
`[-Rq G, -εr)`: above `-εr` the identity certifies the feasible branch, and the verdict is required
to say `true` there.  This is the endpoint reduction the brief asks for; the floor end is
`SoundεOnBracket`'s own lower limit `t = -Rq G`. -/
theorem soundEpsOnBracket_of_runData_interior (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → RunData o G t) :
    QMCLeafB.FinishLine.SoundεOnBracket o := by
  rw [soundEpsOnBracket_iff o]
  intro G t hlo hhi
  by_cases hn : G.n ≤ 1
  · exact soundAt_of_le_one o hn t hlo hhi
  have hn2 : 2 ≤ G.n := by omega
  by_cases hcut : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
  · exact soundAt_of_runData o G t hn2 (hd G t hn2 hlo hcut)
  · -- on the top slice only the feasible clause has content, and the identity supplies it
    have htop' : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) :=
      not_lt.mp hcut
    refine ⟨fun _ => exists_trace_le_of_neg_eps_le G t htop', ?_⟩
    intro hb
    exact absurd (hb ▸ htop G t htop' hhi) (by simp)

/-! ## 6.  Fit check: the result *is* `solution_of_loop`'s `hsound`

The closing consumer is `QMCLeafB.SimPoly.solution_of_loop`, whose hypothesis is
`QMCLeafB.FinishLine.SoundεOnBracket o` (not `Soundε`).  The theorem below applies it to the
`SoundεOnBracket` produced above and lands on `SolutionStatement` — so the two bricks compose with no
adapter. -/

section Fit

open QuantumMaxCutEnergy

local instance instRequestCodingVerdictSound :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **`d9f601e5` from a per-round run bundle.**  `solution_of_loop` with its `hsound` slot filled by
`brick-verdict-sound`. -/
theorem solution_of_loop_via_runData {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p)) = o p.1.1 p.2)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → RunData o G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.SimPoly.solution_of_loop init fuel round verdict hinit hfuel hr hv sizes hsize
    hsize0 o hspec (soundEpsOnBracket_of_runData o hd)

end Fit

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.VerdictSound.soundEpsOnBracket_iff
#print axioms QMCLeafB.VerdictSound.exists_trace_le_of_neg_eps_le
#print axioms QMCLeafB.VerdictSound.eps_nonneg
#print axioms QMCLeafB.VerdictSound.soundAt_false_of_le_floor
#print axioms QMCLeafB.VerdictSound.soundAt_false_at_floor
#print axioms QMCLeafB.VerdictSound.exists_trace_le_zero
#print axioms QMCLeafB.VerdictSound.Rq_eq_zero_of_le_one
#print axioms QMCLeafB.VerdictSound.wMatrix_eq_zero_of_le_one
#print axioms QMCLeafB.VerdictSound.soundAt_of_le_one
#print axioms QMCLeafB.VerdictSound.soundAt_of_runData
#print axioms QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData
#print axioms QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior
#print axioms QMCLeafB.VerdictSound.solution_of_loop_via_runData

end QMCLeafB.VerdictSound


