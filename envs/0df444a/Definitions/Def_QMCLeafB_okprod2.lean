-- Prove2me | Definitions.Def_QMCLeafB_okprod2
-- name    : QMCLeafB_okprod2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:37:40.531881+00:00
-- url     : https://prove2.me/theorems/4d599f50-2a9a-490f-a120-62a7c8610537
-- title:
--   QMCLeafB okprod2
-- statement:
--   Copyright: phase 22, swarm `smw1ntur6`, member m8, direction `ok-production` (dir 6).
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_endgame_m2
import Definitions.Def_QMCLeafB_verdbridge
import Definitions.Def_QMCLeafB_emptybody
import Definitions.Def_QMCLeafB_residbundle_m7
/-
Copyright: phase 22, swarm `smw1ntur6`, member m8, direction `ok-production` (dir 6).

# The ok-branch of the crater is EMPTY

`QMCLeafB.EndgameM2.CoreDataG` is the supplier-friendly residual of the campaign: at every interior
`(G,t)` the supplier hands over a code stream `X`, an `ok` stream, the cut records at the `false`
rounds and the two drift budgets at those rounds.  Read naively the drift slots look like a per-round
analytic obligation on the whole run, i.e. the "crater" that `Check_cutbudget_m8` refuted for the
trace-direction stream at every multiplier.

The point of this file: **at a point where the leaf's bit is `true` the drift slots cost nothing.**
`ok`, `marg` and `c` are *free* fields of `CoreDataG`; the only thing the structure pins them to is
`hverdict : o G t = anyOk ok (K·m)`.  So take `ok ≡ true`: both drift slots become vacuous, the cut
records are never read, and the whole point reduces to a *single* member certificate at a *single*
round (`OkPoint.hmem`).  Freezing the code stream at that round (`X ≡ x`) makes the certificate
available at every round below the horizon, which is all `hmem` asks.

Consequences delivered here:

* §1 `coreDataG_of_okPoint` — the reduction: one member below the horizon + verdict `true`
  ⟹ `CoreDataG`.  No budget, no normal, no multiplier, no stream.
* §2 extraction — `okPoint_of_mem_round`, `coreDataG_of_run` (from a run's own `ok` stream and its
  per-round member certificates, i.e. exactly `BundleHWin.hmem`'s shape), `okPoint_of_window_member`.
* §3 `coreDataG_forces_engine_trace` — at a `false` round, `CoreDataG`'s `hdriftd` *is* the engine
  trace ceiling `diagSum (Cat k) ≤ n(1 - dq/4)` (m7's `window_forces_engine_trace`, restated at the
  supplier-friendly shape and its own `gStream`).  `hTrc` is an *equality* with no hypothesis at the
  run's centres, so the trace slot carries no information: the crater is the drift slot, nothing else.
* §4 `okPoint_of_okV` — m4's `relaxMem_diagPinch_of_okV` (the program's lower-body `ok` answer *is* a
  member certificate) plugged in.  The ok lane's whole residue is the *state coherence plugs* — a
  run-of-program invariant, not an analytic budget.
* §5 `ok_false_below_horizon_of_verdict_false`, `verdict_false_forces_window_trace` — where the crater
  actually sits: at the `false`-bit points, the supplied stream must beat the ceiling at every round
  of the window.
* §6 non-vacuity at `(G₀, -1/2)` through the new route (`RecordsM2.relaxMem_pinch_Q₀`).
* §7 the split residual `OkSupply + RefutedSupply ⟹ ResidG`, and `residH_of_supplies` at the shape
  `FlagsM5.solution_statement_of_residH` consumes.
* §8 sharpness at the empty point `(G₀, -99999/100000)`: `OkPoint` and the `true` bit are empty, so
  the ok lane cannot be over-applied to a refuted point.
* §9 the interface direction 7 consumes: `residH_of_supplies` at the shape
  `FlagsM5.solution_statement_of_residH` takes.
* §10 the crater reaches **feasible** points: at `(G₁, t₁)` (`Check_emptybody_m5` §5) the body is
  nonempty but no matrix of pinched diagonal is a member, so every `CoreDataG` there carries the
  `false` bit.  General form `coreDataG_bit_false_of_no_pinched_member`; the program form
  `oracleV_not_ok_at_G₁` says no round of the run can answer `ok` at `(G₁, t₁)`.
* §11 the ok lane's residue in the campaign's own vocabulary: `HonData`/`HonSupply` — the run's code
  and `ok` streams, their symmetry, the bit read-out `hverdict`, and **`hon`** (an `ok` round below
  the horizon is a canonical member round).  `okSupply_of_hon` + `residWin_of_hon_and_refuted`: the
  ok half of the leaf is `hon`, which `Check_verdbridge_m4` already proves at the lower-body round.

**The named residual of this file**: `RefutedSupply oW paramsKbc2` (`oW` = the repointed roundW bit),
i.e. the crater at the `false`-bit points — empty bodies *and* `(G₁, t₁)`.  Everything else at the
shape level is closed here.

Nothing here touches `FlagsM5`/`DriftExact` shapes, so no locked stroke moves.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.OkProd_M8

open QuantumMaxCutEnergy

/-! ## 1.  The ok point: one frozen member certificate

`CoreDataG`'s `hmem` slot is indexed by the round but its centre is `cXst G.n X P.dq k`, i.e. the
pinch of the *coded* state at that round.  A constant code makes that centre constant, so one
certificate serves every round below the horizon. -/

/-- **The frozen-code ok point.**  A single code `x` whose pinched matrix is a member of the relaxed
body, plus the (unavoidable) fact that the horizon is a positive number of rounds. -/
structure OkPoint (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Type where
  /-- the frozen row-major code -/
  x : List ℚ
  /-- its matrix is symmetric -/
  hsym : (QMCLeafB.StateDiag.stMat G.n x)ᵀ = QMCLeafB.StateDiag.stMat G.n x
  /-- **the one member certificate**: the pinched frozen centre is a member -/
  hmem : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
    (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat G.n x) P.dq)
    (t - QMCLeafB.RundataCert.eps G) P.dq
  /-- the horizon carries at least one round -/
  hKm : 0 < P.K * P.m

/-- **The reduction.**  At a point whose verdict bit is `true`, `CoreDataG` follows from one member
certificate: take the all-`ok` stream (so every cut-side slot is vacuous) and the frozen code (so the
member certificate is available below the horizon). -/
def coreDataG_of_okPoint {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : OkPoint G t P) (hT : o G t = true) :
    QMCLeafB.EndgameM2.CoreDataG o G t P hn where
  X := fun _ => D.x
  hsym := fun _ => D.hsym
  ok := fun _ => true
  hmem := fun k _ _ => D.hmem
  C := fun _ h => absurd h (by simp)
  marg := fun _ => 1
  hmarg := fun _ h => absurd h (by simp)
  c := fun _ _ => 0
  hcEq := fun _ h => absurd h (by simp)
  hdriftc := fun _ h => absurd h (by simp)
  hdriftd := fun _ h => absurd h (by simp)
  hverdict := by
    rw [hT]
    exact ((QMCLeafB.SimLoop.anyOk_eq_true_iff (fun _ => true) (P.K * P.m)).2
      ⟨0, D.hKm, rfl⟩).symm

#print axioms QMCLeafB.OkProd_M8.coreDataG_of_okPoint

/-- The producer is a *function* of the bit: at the all-`true` bit the ok shape is inhabited exactly
when a member below the horizon exists. -/
theorem nonempty_coreDataG_iff_of_verdict_true {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n} :
    Nonempty (OkPoint G t P) →
    Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) G t P hn) :=
  fun ⟨D⟩ => ⟨coreDataG_of_okPoint D rfl⟩

#print axioms QMCLeafB.OkProd_M8.nonempty_coreDataG_iff_of_verdict_true

/-! ## 2.  Round extraction

`OkPoint` at an arbitrary round of an arbitrary code family.  Two conversions are needed: the
`RelaxMem` at `cXst` (the round's own centre) must be read at the pinch, and the pointwise symmetry
of the run's matrices must be read as matrix symmetry. -/

/-- Matrix symmetry from the entrywise form (the shape the program's invariants speak). -/
theorem transpose_eq_of_pointwise {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ}
    (h : ∀ i j, M i j = M j i) : Mᵀ = M := by
  ext i j
  rw [Matrix.transpose_apply]
  exact (h i j).symm

#print axioms QMCLeafB.OkProd_M8.transpose_eq_of_pointwise

/-- Entrywise symmetry from matrix symmetry. -/
theorem pointwise_of_transpose_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ}
    (h : Mᵀ = M) : ∀ i j, M i j = M j i := by
  intro i j
  have := congrFun (congrFun h i) j
  rw [Matrix.transpose_apply] at this
  exact this.symm

#print axioms QMCLeafB.OkProd_M8.pointwise_of_transpose_eq

/-- **The ok point at a named round of a code family.**  Nothing about the *other* rounds is used:
the frozen code is the state at round `k₀`. -/
def okPoint_of_mem_round {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (X : ℕ → List ℚ) (k₀ : ℕ) (hk₀ : k₀ < P.K * P.m)
    (hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ
      = QMCLeafB.StateDiag.stMat G.n (X k))
    (hmem : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
      (QMCLeafB.RecordsM2.cXst G.n X P.dq k₀) (t - QMCLeafB.RundataCert.eps G) P.dq) :
    OkPoint G t P where
  x := X k₀
  hsym := hsym k₀
  hmem := hmem
  hKm := lt_of_le_of_lt (Nat.zero_le k₀) hk₀

#print axioms QMCLeafB.OkProd_M8.okPoint_of_mem_round

/-- **The ok-branch from a run's own stream.**  The inputs are exactly `BundleHWin`'s `hmem` (member
certificates at the `ok` rounds below the horizon), `BundleHWin`'s `hverdict`, and the verdict being
`true`.  No drift slot appears. -/
def coreDataG_of_run {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (X : ℕ → List ℚ) (ok : ℕ → Bool)
    (hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
        (QMCLeafB.RecordsM2.cXst G.n X P.dq k) (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hv : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) (hT : o G t = true) :
    QMCLeafB.EndgameM2.CoreDataG o G t P hn := by
  have h1 : QMCLeafB.SimLoop.anyOk ok (P.K * P.m) = true := by rw [← hv]; exact hT
  have hex : ∃ k, k < P.K * P.m ∧ ok k = true :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff ok (P.K * P.m)).1 h1
  let k₀ : ℕ := Classical.choose hex
  have hk₀ : k₀ < P.K * P.m := (Classical.choose_spec hex).1
  have hok : ok k₀ = true := (Classical.choose_spec hex).2
  exact coreDataG_of_okPoint (okPoint_of_mem_round X k₀ hk₀ hsym (hmem k₀ hk₀ hok)) hT

#print axioms QMCLeafB.OkProd_M8.coreDataG_of_run

/-- **The window bundle's own ok side feeds the producer.**  `BundleHWin.hmem` is stated at the
bundle's queried centres `W.cX`; a code realization of one such centre gives the ok point.  This is
the adapter direction 7 uses when it zips the ok lane into the run bundle. -/
def okPoint_of_window_member {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (X : ℕ → List ℚ) {k₀ : ℕ} (hk₀ : k₀ < P.K * P.m)
    (hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (hmem : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
      (QMCLeafB.RecordsM2.cXst G.n X P.dq k₀) (t - QMCLeafB.RundataCert.eps G) P.dq) :
    OkPoint G t P :=
  okPoint_of_mem_round X k₀ hk₀ hsym hmem

#print axioms QMCLeafB.OkProd_M8.okPoint_of_window_member

/-! ## 3.  What the drift slot *is* at a `false` round (the crater sits there)

`CoreDataG.hdriftd` at a `false` round reads, through `DriftExact.stated_iff_trace`, as a bound on
the engine's own centre — and the query centre's diagonal is the pinch value *exactly*, with no
hypothesis (`RecordsM2.cXst_trace`).  So the slot is the unconditional ceiling
`diagSum (Cat k) ≤ n(1 - dq/4)` at that round. -/

/-- **`hdriftd` at a `false` round forces the engine trace ceiling.**  m7's
`window_forces_engine_trace`, restated at the supplier-friendly shape and at the shape's own
`gStream` (the bound is therefore not an artefact of the bundle encoding). -/
theorem coreDataG_forces_engine_trace {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) {k : ℕ} (hok : D.ok k = false) :
    QMCLeafB.DriftExact.diagSum
        (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.EndgameM2.gStream G P hn D.c D.marg) k)
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) := by
  have h1 := (QMCLeafB.DriftExact.stated_iff_trace _ (QMCLeafB.RecordsM2.cXst G.n D.X P.dq k)).1
    (D.hdriftd k hok)
  have h2 : (∑ i : Fin G.n, ((QMCLeafB.RecordsM2.cXst G.n D.X P.dq k i i : ℚ) : ℝ))
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) := by
    have hdiag : ∀ i : Fin G.n,
        ((QMCLeafB.RecordsM2.cXst G.n D.X P.dq k i i : ℚ) : ℝ)
          = ((1 - P.dq / 4 : ℚ) : ℝ) := fun i => by
      rw [QMCLeafB.RecordsM2.cXst_diag]
    rw [Finset.sum_congr rfl (fun i _ => hdiag i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    exact le_of_eq (by ring)
  linarith

#print axioms QMCLeafB.OkProd_M8.coreDataG_forces_engine_trace

/-- **The ceiling is not an artefact of `hTrc`**: at the run's own centres `hTrc` holds with
*equality* and no hypothesis at all, so the trace slot of the shape carries no information — the
only content of `hdriftd` is the engine bound above. -/
theorem hTrc_at_cXst (n : ℕ) (X : ℕ → List ℚ) (dq : ℚ) (k : ℕ) :
    ∑ i, QMCLeafB.RecordsM2.cXst n X dq k i i = (n : ℚ) * (1 - dq / 4) :=
  QMCLeafB.RecordsM2.cXst_trace n X dq k

#print axioms QMCLeafB.OkProd_M8.hTrc_at_cXst

/-! ## 4.  m4's lower-body `ok` answer plugged into the producer

`Check_verdbridge_m4`'s `relaxMem_diagPinch_of_okV` is the ok-branch certificate of the *program*: an
`ok` answer of `OkLower.oracleV` at a state means the state's own matrix is exactly PSD with unit
diagonal and sits under the level, so its pinched centre is a member.  Composed with §1 this is the
whole ok lane: the residual left over is the *state coherence plugs* (`hN`, `hlenA`, `hlenX`, `hA`,
`hsym`, `hpiv`, `hT`, `hdq`), a run-of-program invariant — not an analytic budget. -/

/-- **The ok point from a program state's `ok` answer.** -/
def okPoint_of_okV {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {s : QMCLeafB.RoundProgram.RSt} {acc : QMCLeafB.PivotProgram.Acc} {k₀ : ℕ}
    (hk₀ : k₀ < P.K * P.m)
    (hN : QMCLeafB.RoundProgram.stN s = G.n)
    (hlenA : G.n ≤ (QMCLeafB.RoundProgram.stA s).length)
    (hlenX : G.n ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hA : QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA s)
      = QMCLeafB.Finalization.wMatrixQ G)
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s) i j
      = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s) j i)
    (hok : (QMCLeafB.OkLower.oracleV s).1 = false)
    (hpiv : (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX s), acc)).1 = false)
    (hdqpos : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hT : QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s
      = t - QMCLeafB.RundataCert.eps G)
    (hdq : QMCLeafB.OkLower.dqOf s = P.dq) :
    OkPoint G t P := by
  refine okPoint_of_mem_round (fun _ => QMCLeafB.RoundProgram.stX s) k₀ hk₀ ?_ ?_
  · intro k
    exact transpose_eq_of_pointwise hsym
  · exact QMCLeafB.VerdictBridge.relaxMem_diagPinch_of_okV hN hlenA hlenX hA
      (fun i => QMCLeafB.RecordsM2.wMatrixQ_diag G i) hsym hok hpiv hdqpos hdq4 hT hdq

#print axioms QMCLeafB.OkProd_M8.okPoint_of_okV

/-! ## 5.  Where the crater actually sits: every `false` round below the horizon

The complement of §1.  `anyOk` sees only the window `k < K·m`, so at a point whose bit is `false`
*every* round of the window is a `false` round — hence, by §3, every round of the window carries the
engine trace ceiling.  This is the sharpest form of the crater at the supplier shape: the refuted
lane must exhibit a stream whose *whole-window* trace beats `n(1 - dq/4)`, at the stream's own
`gStream`. -/

/-- `anyOk` is `true` as soon as one round of the window is `ok`. -/
theorem anyOk_eq_true_of_lt (ok : ℕ → Bool) {k T : ℕ} (hk : k < T) (h : ok k = true) :
    QMCLeafB.SimLoop.anyOk ok T = true :=
  (QMCLeafB.SimLoop.anyOk_eq_true_iff ok T).2 ⟨k, hk, h⟩

#print axioms QMCLeafB.OkProd_M8.anyOk_eq_true_of_lt

/-- **At a `false` point the supplied stream is `false` on the whole window.** -/
theorem ok_false_below_horizon_of_verdict_false
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) (h : o G t = false) :
    ∀ k, k < P.K * P.m → D.ok k = false := by
  intro k hk
  have hnot : ¬ D.ok k = true := by
    intro htrue
    have h1 : QMCLeafB.SimLoop.anyOk D.ok (P.K * P.m) = true :=
      anyOk_eq_true_of_lt D.ok hk htrue
    rw [D.hverdict, h1] at h
    exact Bool.noConfusion h
  cases hb : D.ok k with
  | false => rfl
  | true => exact absurd hb hnot

#print axioms QMCLeafB.OkProd_M8.ok_false_below_horizon_of_verdict_false

/-- **The refuted-point window-wide trace ceiling.**  Any `CoreDataG` at a point whose bit is `false`
forces the engine trace ceiling at *every* round below the horizon, at whatever normal/margin stream
it supplies.  (m8's `Check_cutbudget_m8` kills the trace-direction dilation stream against exactly
this ceiling from round 4 on, so the refuted lane is a genuine satisfiability problem over the
stream — and the ok lane, §1, is not.) -/
theorem verdict_false_forces_window_trace
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) (h : o G t = false) :
    ∀ k, k < P.K * P.m →
      QMCLeafB.DriftExact.diagSum
          (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.EndgameM2.gStream G P hn D.c D.marg) k)
        ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) :=
  fun k hk => coreDataG_forces_engine_trace D (ok_false_below_horizon_of_verdict_false D h k hk)

#print axioms QMCLeafB.OkProd_M8.verdict_false_forces_window_trace

/-! ## 6.  Non-vacuity at `(G₀, -1/2)` through the new route

The ok point of `Check_endgame_m2` §14, rebuilt from `RecordsM2.relaxMem_pinch_Q₀` and the frozen
code: an independent check that §1's hypothesis `OkPoint` is satisfiable at the campaign family (and
therefore that the producer is not a vacuous restatement). -/

/-- **`OkPoint` is inhabited at `(G₀, -1/2)`.** -/
def okPoint_G₀_half :
    OkPoint QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) where
  x := QMCLeafB.RecordsM2.Q₀code
  hsym := by
    rw [QMCLeafB.RecordsM2.stMat_Q₀code]
    exact QMCLeafB.FlagsM5.Q₀_transpose
  hmem := by
    rw [QMCLeafB.RecordsM2.stMat_Q₀code]
    exact QMCLeafB.RecordsM2.relaxMem_pinch_Q₀
  hKm := lt_of_lt_of_le Nat.zero_lt_one
    (QMCLeafB.UnionShallow.one_le_Kbc2_mul QMCLeafB.ResidRefute.G₀)

#print axioms QMCLeafB.OkProd_M8.okPoint_G₀_half

/-- **The ok-branch producer fires at `(G₀, -1/2)`.** -/
theorem coreDataG_G₀_half_via_okprod :
    Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :=
  ⟨coreDataG_of_okPoint okPoint_G₀_half rfl⟩

#print axioms QMCLeafB.OkProd_M8.coreDataG_G₀_half_via_okprod

/-! ## 7.  The split residual

`EndgameM2.ResidG` splits, with no overlap and no gap, into the ok supply of this file and the
refuted supply of the crater lane.  Direction 7 (integration) consumes this statement: the ok half
is settled here, the refuted half is the only open analytic question. -/

/-- The ok half of `ResidG`: at every interior point whose bit is `true`, one frozen member
certificate. -/
abbrev OkSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = true → OkPoint G t (Pfam G)

/-- The refuted half of `ResidG`: the crater lane (`crater-construction` / `crater-satisfiability`),
which must supply a stream whose whole-window trace beats the ceiling (`verdict_false_forces_window_trace`
says that is exactly what is being asked). -/
abbrev RefutedSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false → QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn

/-- **The zip: the two supplies give the supplier-friendly residual.** -/
def residG_of_supplies {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (Hok : OkSupply o Pfam) (Href : RefutedSupply o Pfam) :
    QMCLeafB.EndgameM2.ResidG o Pfam := by
  intro G t hn hlo hhi
  by_cases hb : o G t = true
  · exact coreDataG_of_okPoint (Hok G t hn hlo hhi hb) hb
  · refine Href G t hn hlo hhi ?_
    cases hc : o G t with
    | false => rfl
    | true => exact absurd hc hb

#print axioms QMCLeafB.OkProd_M8.residG_of_supplies

/-! ## 8.  Sharpness at the empty point

Two anchors around §7's split, both at `G₀`:

* at the **ok point** `(G₀, -1/2)` the ok shape is inhabited (§6), and
* at the **refuted point** `(G₀, t₀)`, `t₀ = -99999/100000`, the ok shape is *uninhabited*, and so is
  `CoreDataG` at the `true` bit.  So `OkSupply` is not a weakening one can get for free: it is exactly
  "the pinched body is nonempty at a point whose bit is `true`", and the refuted half of §7 carries
  the whole analytic residue.

The refuted point is `Check_emptybody_m5`'s empty-body point (`not_relaxMem_G₀` is unconditional in
the centre). -/

/-- **`OkPoint` is uninhabited at the refuted point `(G₀, -99999/100000)`.** -/
theorem not_nonempty_okPoint_G₀_bottom :
    ¬ Nonempty (OkPoint QMCLeafB.ResidRefute.G₀ (-(99999 / 100000))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)) := by
  rintro ⟨D⟩
  exact QMCLeafB.EmptyBodyM5.not_relaxMem_G₀ _ D.hmem

#print axioms QMCLeafB.OkProd_M8.not_nonempty_okPoint_G₀_bottom

/-- **`CoreDataG` at the `true` bit is uninhabited at the refuted point.**  The all-`true` stream
needs one member below the horizon, and there is none anywhere; so the refuted lane *must* run at the
`false` bit, where §5 forces the window-wide engine trace ceiling. -/
theorem not_coreDataG_true_G₀_bottom (hn : 2 ≤ QMCLeafB.ResidRefute.G₀.n) :
    ¬ Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) QMCLeafB.ResidRefute.G₀
      (-(99999 / 100000)) (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) hn) := by
  rintro ⟨D⟩
  have hany : QMCLeafB.SimLoop.anyOk D.ok
      ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m) = true :=
    D.hverdict.symm
  obtain ⟨k₀, hk₀, hok⟩ :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff D.ok _).1 hany
  exact QMCLeafB.EmptyBodyM5.not_relaxMem_G₀ _ (D.hmem k₀ hk₀ hok)

#print axioms QMCLeafB.OkProd_M8.not_coreDataG_true_G₀_bottom

/-! ## 9.  The interface direction 7 consumes

`{OkSupply, RefutedSupply, hrmax} → ResidH`, the shape `FlagsM5.solution_statement_of_residH`
takes.  Nothing else is left at the shape level. -/

/-- **The two supplies give the window/bundle residual.** -/
def residH_of_supplies {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n), 0 < (Pfam G).rmax)
    (Hok : OkSupply o Pfam) (Href : RefutedSupply o Pfam) :
    QMCLeafB.FlagsM5.ResidH o Pfam :=
  QMCLeafB.EndgameM2.residH_of_supplied hrmax (residG_of_supplies Hok Href)

#print axioms QMCLeafB.OkProd_M8.residH_of_supplies

/-! ## 10.  The ok lane cannot be widened to "the body is nonempty"

§5 of `Check_emptybody_m5` exhibits `(G₁, t₁)` where the relaxed body is **nonempty**
(`body_nonempty_G₁`, witness `Q₁` with unit diagonal) and yet **no pinched matrix is a member**
(`no_pinched_member_G₁`).  Since `CoreDataG`'s `hmem` is stated at the *pinched* centre `cXst` —
whose diagonal is `1 - dq/4` by definition, with no hypothesis — the ok lane is dead at `(G₁, t₁)`:
there the residual *must* run at the `false` bit, i.e. through the crater.

This is the verdict-lane counterpart of m1's `bit_false_at_all_bottoms`, at a point where the
relaxation is *feasible*: the constraint comes from the pinch, not from emptiness. -/

/-- **A point with no pinched member forces the bit to `false`.**  General form: at any `(G,t)` where
no matrix of pinched diagonal is a member, *every* `CoreDataG` carries the `false` bit (an all-`true`
window would need one member at a pinched centre). -/
theorem coreDataG_bit_false_of_no_pinched_member
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (h : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ, (∀ i, Q i i = 1 - P.dq / 4) →
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) : o G t = false := by
  have hnot : ¬ o G t = true := by
    intro hT
    have hany : QMCLeafB.SimLoop.anyOk D.ok (P.K * P.m) = true := by
      rw [← D.hverdict]; exact hT
    obtain ⟨k₀, hk₀, hok⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff D.ok (P.K * P.m)).1 hany
    exact h (QMCLeafB.RecordsM2.cXst G.n D.X P.dq k₀)
      (fun i => QMCLeafB.RecordsM2.cXst_diag G.n D.X P.dq k₀ i) (D.hmem k₀ hk₀ hok)
  cases hb : o G t with
  | false => rfl
  | true => exact absurd hb hnot

#print axioms QMCLeafB.OkProd_M8.coreDataG_bit_false_of_no_pinched_member

/-- **`OkPoint` is uninhabited at `(G₁, t₁)`** — nonempty body, no pinched member. -/
theorem not_nonempty_okPoint_G₁ :
    ¬ Nonempty (OkPoint QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁)) := by
  rintro ⟨D⟩
  exact QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ _
    (fun i => QMCLeafB.CentreAdm.diagPinch_diag _ _ i) D.hmem

#print axioms QMCLeafB.OkProd_M8.not_nonempty_okPoint_G₁

/-- **The bit is `false` at `(G₁, t₁)`.**  Every `CoreDataG` at that point — where the relaxed body is
*nonempty* — carries the `false` bit, so the crater lane is not confined to empty bodies. -/
theorem coreDataG_G₁_bit_false
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {hn : 2 ≤ QMCLeafB.EmptyBodyM5.G₁.n}
    (D : QMCLeafB.EndgameM2.CoreDataG o QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁) hn) :
    o QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000) = false :=
  coreDataG_bit_false_of_no_pinched_member
    (fun Q hQ => QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ Q hQ) D

#print axioms QMCLeafB.OkProd_M8.coreDataG_G₁_bit_false

/-- **The `true` bit is uninhabited at `(G₁, t₁)`.** -/
theorem not_coreDataG_true_G₁ (hn : 2 ≤ QMCLeafB.EmptyBodyM5.G₁.n) :
    ¬ Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) QMCLeafB.EmptyBodyM5.G₁
      (-(2 : ℚ) + 71 / 1520000)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁) hn) := by
  rintro ⟨D⟩
  have h := coreDataG_G₁_bit_false D
  exact Bool.noConfusion h

#print axioms QMCLeafB.OkProd_M8.not_coreDataG_true_G₁

/-- **The lower-body oracle cannot answer `ok` at `(G₁, t₁)`.**  Composing §4's plug with the
uninhabitation above: any run state at `(G₁, t₁)` with the coherence plugs has `oracleV` returning a
cut, not an `ok`.  So the campaign's descent must run at `(G₁, t₁)` — a *design constraint on the
program at a feasible point*, machine-checked, and the reason the false-bit lane has to cover it. -/
theorem oracleV_not_ok_at_G₁ {s : QMCLeafB.RoundProgram.RSt} {acc : QMCLeafB.PivotProgram.Acc}
    (hN : QMCLeafB.RoundProgram.stN s = QMCLeafB.EmptyBodyM5.G₁.n)
    (hlenA : QMCLeafB.EmptyBodyM5.G₁.n ≤ (QMCLeafB.RoundProgram.stA s).length)
    (hlenX : QMCLeafB.EmptyBodyM5.G₁.n ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hA : QMCLeafB.StateDiag.stMat QMCLeafB.EmptyBodyM5.G₁.n (QMCLeafB.RoundProgram.stA s)
      = QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁)
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat QMCLeafB.EmptyBodyM5.G₁.n
        (QMCLeafB.RoundProgram.stX s) i j
      = QMCLeafB.StateDiag.stMat QMCLeafB.EmptyBodyM5.G₁.n (QMCLeafB.RoundProgram.stX s) j i)
    (hpiv : (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (QMCLeafB.EmptyBodyM5.G₁.n,
        QMCLeafB.RoundProgram.stX s), acc)).1 = false)
    (hT : QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s
      = (-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
    (hdq : QMCLeafB.OkLower.dqOf s
      = (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq) :
    (QMCLeafB.OkLower.oracleV s).1 = true := by
  have hKm : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).K
      * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).m :=
    lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul _)
  have hdqpos : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq :=
    QMCLeafB.RecordM2.dq_pos_paramsKbc2 _
  have hdq4 : (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq ≤ 4 :=
    le_of_lt (QMCLeafB.RecordM2.dq_lt_four_paramsKbc2 _)
  cases hb : (QMCLeafB.OkLower.oracleV s).1 with
  | true => rfl
  | false =>
      exact absurd
        ⟨okPoint_of_okV (G := QMCLeafB.EmptyBodyM5.G₁) (t := (-(2 : ℚ) + 71 / 1520000))
          (P := QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁)
          (s := s) (acc := acc) (k₀ := 0) hKm hN hlenA hlenX hA hsym hb hpiv
          hdqpos hdq4 hT hdq⟩
        not_nonempty_okPoint_G₁

#print axioms QMCLeafB.OkProd_M8.oracleV_not_ok_at_G₁

/-- **The two supplies reach the windowed residual** (`ResidWin`, the shape both
`FlagsM5.solution_statement_of_residH` and the roundW strokes consume). -/
def residWin_of_supplies {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n), 0 < (Pfam G).rmax)
    (Hok : OkSupply o Pfam) (Href : RefutedSupply o Pfam) :
    QMCLeafB.ResidBundle_M7.ResidWin o Pfam :=
  QMCLeafB.ResidBundle_M7.residWin_of_residH (residH_of_supplies hrmax Hok Href)

#print axioms QMCLeafB.OkProd_M8.residWin_of_supplies

/-! ## 11.  The ok lane's residue is exactly `hon`

`FlagsM5.relaxMem_of_flagOf_true` turns a `true` canonical flag into its member certificate, so §2's
`hmem` hypothesis can be replaced by the campaign's own **`hon`** slot: "a round the program reported
`ok` is a member round".  At the repointed lower-body round `hon` is `Check_verdbridge_m4`'s
`flag_true_of_okV` / `hon_slot`; so the ok lane asks for nothing beyond a slot the campaign already
proves elsewhere.  This is the cleanest form of my residual. -/

/-- **`CoreDataG` from `hon`.** -/
def coreDataG_of_hon {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (X : ℕ → List ℚ) (ok : ℕ → Bool)
    (hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (hon : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true)
    (hv : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) (hT : o G t = true) :
    QMCLeafB.EndgameM2.CoreDataG o G t P hn :=
  coreDataG_of_run X ok hsym
    (fun k hk hok => QMCLeafB.FlagsM5.relaxMem_of_flagOf_true G t P
      (QMCLeafB.RecordsM2.cXst G.n X P.dq) k (hon k hk hok)) hv hT

#print axioms QMCLeafB.OkProd_M8.coreDataG_of_hon

/-- The run's own read-out together with `hon`, as data (it must be a `Type`: the ok lane is a
*construction*, so the witness round has to be extractable). -/
structure HonData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Type where
  /-- the run's coded state stream -/
  X : ℕ → List ℚ
  /-- the run's own `ok` stream -/
  ok : ℕ → Bool
  /-- the run's states are symmetric -/
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- **`hon`**: an `ok` round below the horizon is a member round of the canonical flag stream -/
  hon : ∀ k, k < P.K * P.m → ok k = true →
    QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true
  /-- the leaf's bit is the run's read-out -/
  hv : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-- **`hon` at the run's read-out gives the ok point.** -/
def okPoint_of_honData {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (D : HonData o G t P) (hT : o G t = true) :
    OkPoint G t P := by
  have h1 : QMCLeafB.SimLoop.anyOk D.ok (P.K * P.m) = true := by rw [← D.hv]; exact hT
  have hex : ∃ k, k < P.K * P.m ∧ D.ok k = true :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff D.ok (P.K * P.m)).1 h1
  let k₀ : ℕ := Classical.choose hex
  have hk₀ : k₀ < P.K * P.m := (Classical.choose_spec hex).1
  have hok : D.ok k₀ = true := (Classical.choose_spec hex).2
  exact okPoint_of_mem_round D.X k₀ hk₀ D.hsym
    (QMCLeafB.FlagsM5.relaxMem_of_flagOf_true G t P
      (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k₀ (D.hon k₀ hk₀ hok))

#print axioms QMCLeafB.OkProd_M8.okPoint_of_honData

/-- The ok supply phrased at `hon` and the run's own read-out. -/
abbrev HonSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = true → HonData o G t (Pfam G)

/-- **`hon` on the run's read-out gives the ok supply.**  Nothing analytic: this is §1 composed with
`FlagsM5.relaxMem_of_flagOf_true`. -/
def okSupply_of_hon {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : HonSupply o Pfam) : OkSupply o Pfam :=
  fun G t hn hlo hhi hT => okPoint_of_honData (H G t hn hlo hhi hT) hT

#print axioms QMCLeafB.OkProd_M8.okSupply_of_hon

/-- **The terminal interface: `hon` + the refuted supply give the windowed residual.**  Direction 7's
spine: `{hon at the run's read-out, refuted-point stream, 0 < rmax} ⟹ ResidWin`, and `ResidWin` is what
the locked d9f601e5 strokes consume. -/
def residWin_of_hon_and_refuted {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n), 0 < (Pfam G).rmax)
    (Hhon : HonSupply o Pfam) (Href : RefutedSupply o Pfam) :
    QMCLeafB.ResidBundle_M7.ResidWin o Pfam :=
  residWin_of_supplies hrmax (okSupply_of_hon Hhon) Href

#print axioms QMCLeafB.OkProd_M8.residWin_of_hon_and_refuted

end QMCLeafB.OkProd_M8


