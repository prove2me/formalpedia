-- Prove2me | Definitions.Def_QMCLeafB_fam33
-- name    : QMCLeafB_fam33
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:31:51.767427+00:00
-- url     : https://prove2.me/theorems/7b4c2f9e-9602-4b46-b479-8e8af091e448
-- title:
--   QMCLeafB fam33
-- statement:
--   `Check_fam33_m5` — phase 33, member m5, direction `family-assembly` (slot 4).
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sound31
import Definitions.Def_QMCLeafB_refuted_m3
/-
  `Check_fam33_m5` — phase 33, member m5, direction `family-assembly` (slot 4).

  Scope: the **assembly end** of the `Sound31` interface,

      `solution_of_runPartsFamily (o) (ho) (B : ∀ G t, RunParts o G t (P G)) (hKm)`.

  What this file does, in order:

  * §1 — re-proves the `ok`-stream record (`runParts_of_member`) on this file's import cone, so that
    the two banked record classes (`RefutedM3.runParts_of_emptyBody`, the all-`ok` stream) are both
    available next to `Check_sound31`'s stroke.  (`AsmM8.runParts_of_member` lives on the
    `Definitions.Def_*` cone, which does not co-load with `Solutions.Check_EngineIterates`:
    `Check_sound31`'s cone contains the latter.  This was the first thing checked.)
  * §2 — **the family as stated is EMPTY**: at `G.n = 0` and `t = -Rq/40000 - 1` no record exists
    for any bit and any parameter family.  The reason is exact and structural: every cut round owes
    `(cd k).c ≠ 0` with `(cd k).c : Fin (0*0) → ℚ`, and every `ok` round owes a unit-diagonal PSD
    point whose trace is `0 ≤ t + Rq/40000 = -1`.  Hence `∀ G t, RunParts o G t (P G)` is
    unsatisfiable, `solution_of_runPartsFamily` cannot be applied at any `hKm`, and the phase-33
    charter's "the whole leaf = a poly bit + a record family" needs the repair below.  (This is the
    seventh vacuity in the campaign's series; the first six were caught the same way.)
  * §3 — the repair: the record is only needed on `2 ≤ G.n` (the `n ≤ 1` case is `soundAt_of_le_one`'s,
    which needs no record) and only on the bracket `-Rq ≤ t ≤ 0` (outside it `SoundεOnBracket` says
    nothing).  `soundEpsOnBracket_of_family_le2` / `solution_of_runPartsFamily_le2` are the repaired
    strokes — same proof, two hypotheses weaker.
  * §4 — the dispatch, with **two** residual slots and no more: the `true` bit needs a genuine
    unit-diagonal PSD point at `t + Rq/40000` (`hM`; free on the top slice `t ≥ -Rq/40000`, where the
    identity certifies), the `false` bit needs either an empty body (free, banked) or the leftover
    `hC` record.  Note there is **no** `hE` slot: `runParts_of_emptyBody` needs the bit only where it
    is applied, not an implication `EmptyBody → bit = false`.
  * §5 — the assembled verbatim `d9f601e5` sentence at this interface.

  Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
  `#print axioms` receipts at the end of each section.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QMCLeafB.Fam33M5

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- The request coding of the leaf (local, as everywhere in the campaign). -/
local instance instCodingFam33 : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 0.  The three objects of the interface, spelled once -/

/-- The leaf's slack `εr = Rq G / 40000`. -/
abbrev epsG (G : QuantumMaxCutEnergy.Input) : ℚ := QMCLeafB.EngineRuntime.Rq G / 40000

/-- A **genuine** unit-diagonal PSD point at `t + εr` — the `ok`-round certificate of the record. -/
abbrev MemberAt (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
      (QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ) + ((epsG G : ℚ) : ℝ)

/-- The engine's relaxed body at its own level `t - εr` and tolerance `dq`. -/
abbrev BodyLE (G : QuantumMaxCutEnergy.Input) (t dq : ℚ)
    (X : Matrix (Fin G.n) (Fin G.n) ℝ) : Prop :=
  QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
    ((t : ℝ) - ((epsG G : ℚ) : ℝ)) ((dq : ℚ) : ℝ) X

/-- The body is empty. -/
abbrev BodyEmpty (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ, ¬ BodyLE G t P.dq X

theorem bodyEmpty_iff (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) :
    BodyEmpty G t P ↔
      ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ) X :=
  Iff.rfl

/-! ## 1.  The `ok` stream, on this cone

`Check_asm_m8`'s `runParts_of_member` is on the `Definitions.Def_*` cone, which cannot co-load with
`Check_sound31`'s (`Solutions.Check_EngineIterates` vs `Definitions.Def_QMCLeafB_EngineIterates`
declare the same `Aat.match_1`).  The proof is four lines, so it is redone here. -/

/-- `anyOk` of a constantly-`true` stream is `true`, for a positive horizon. -/
theorem anyOk_const_true (T : ℕ) (hT : 0 < T) :
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) T = true := by
  induction T with
  | zero => exact absurd hT (Nat.lt_irrefl 0)
  | succ k _ => rw [QMCLeafB.SimLoop.anyOk_succ]; rfl

#print axioms QMCLeafB.Fam33M5.anyOk_const_true

/-- **The `M` class of the record family**: bit `true` plus a genuine unit-diagonal PSD point at
`t + εr` gives `RunParts` by the all-`ok` stream.  The cut slots are vacuous, the certificate is the
same point at every round. -/
noncomputable def runParts_of_member {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hKm : 0 < P.K * P.m)
    (hbit : o G t = true) (hmem : MemberAt G t) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  classical
  have hN : 2 ≤ G.n * G.n := by have := hn; nlinarith
  haveI : NeZero (G.n * G.n) := ⟨by omega⟩
  set c : ℕ → Fin (G.n * G.n) → ℚ := fun _ => QMCLeafB.RefutedM3.e₀ (G.n * G.n) with hc
  have hcne : ∀ k : ℕ, c k ≠ 0 := fun _ => QMCLeafB.RefutedM3.e₀_ne (G.n * G.n)
  set cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
    QMCLeafB.RunPartsDilate.runCut G P hn c hcne with hcd
  exact
    { ok := fun _ => true
      cd := cd
      del := fun _ => 0
      hcert := by intro k _ _; exact hmem
      hwit := by intro k _ hok; exact absurd hok (by simp)
      hrho := by intro k _ hok; exact absurd hok (by simp)
      hcne := by intro k _ hok; exact absurd hok (by simp)
      hdel0 := by intro k _ hok; exact absurd hok (by simp)
      hcheck := by intro k _ hok; exact absurd hok (by simp)
      hle := by intro k _ hok; exact absurd hok (by simp)
      hcut := by intro k _ hok; exact absurd hok (by simp)
      hverdict := by
        rw [hbit]
        exact (anyOk_const_true (P.K * P.m) hKm).symm }

#print axioms QMCLeafB.Fam33M5.runParts_of_member

/-- The `M` class really is a *necessary* condition of the record family: every record at a
bit-`true` point exhibits a member.  So `hM` is not an extra assumption of §4 — it is what any
family at the program's bit already carries. -/
theorem memberAt_of_runParts {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (hbit : o G t = true) : MemberAt G t := by
  have h := B.hverdict
  rw [hbit] at h
  obtain ⟨k, hk, hok⟩ :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff B.ok (P.K * P.m)).mp h.symm
  exact B.hcert k hk hok

#print axioms QMCLeafB.Fam33M5.memberAt_of_runParts

/-- **`hM` is free on the top slice of the bracket**: for `t ≥ -εr` the identity is unit-diagonal
PSD with zero trace.  So the member slot is only owed on `-Rq G ≤ t < -εr`. -/
theorem memberAt_of_neg_eps_le (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (ht : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) : MemberAt G t :=
  QMCLeafB.VerdictSound.exists_trace_le_of_neg_eps_le G t ht

#print axioms QMCLeafB.Fam33M5.memberAt_of_neg_eps_le

/-! ## 2.  **The family as stated is empty** — the `G.n = 0` stratum

At `G.n = 0` the constraint matrix is `0 × 0`, so `tr (wMatrix G · X) = 0` for every `X`, and the
run's relaxation has no direction at all: `(cd k).c : Fin (0*0) → ℚ` is the zero function.  Every
round must therefore report `ok`, and the `ok` certificate at the level `t + εr` must be
nonnegative.  Taking `t < -εr` kills the family.  This is a defect of the *stroke*, not of the leaf:
`soundAt_of_le_one` already settles `n ≤ 1` with no record, and the bracket never asks for a
non-bracketed `t`. -/

/-- The weightless single-vertex-free input: `n = 0`, empty weight function. -/
def Gzero : QuantumMaxCutEnergy.Input where
  n := 0
  weights := fun e => Fin.elim0 e.1.1

/-- **No record at a `0 × 0` input below `-εr`.**  Every round would have to be `ok` (`(cd k).c = 0`
is forced), and the `ok` certificate's trace is `0`, which must be `≤ t + εr < 0`. -/
theorem no_runParts_of_zero {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (G : QuantumMaxCutEnergy.Input) (hG : G.n = 0)
    (P : QMCLeafB.FinalStroke.RunParams G) (hKm : 0 < P.K * P.m)
    (t : ℚ) (ht : (t : ℝ) + ((epsG G : ℚ) : ℝ) < 0) :
    ¬ Nonempty (QMCLeafB.FinalStroke.RunParts o G t P) := by
  rintro ⟨B⟩
  have h0 : G.n * G.n = 0 := by rw [hG]
  -- every round reports `ok`, because a `cut` needs a nonzero code in `Fin (0*0) → ℚ`
  have hok : ∀ k, k < P.K * P.m → B.ok k = true := by
    intro k hk
    rcases hb : B.ok k with _ | _
    · exfalso
      refine B.hcne k hk hb ?_
      funext i
      exact absurd i.isLt (by omega)
    · rfl
  obtain ⟨X, _hX, htr⟩ := B.hcert 0 hKm (hok 0 hKm)
  have htr0 : (QMCLeafB.wMatrix G * X).trace = 0 := by
    have hE : IsEmpty (Fin G.n) := ⟨fun i => by have := i.isLt; omega⟩
    simp [Matrix.trace]
  rw [htr0] at htr
  linarith

#print axioms QMCLeafB.Fam33M5.no_runParts_of_zero

/-- **The `RunParts` family is uninhabited** — for every bit and every parameter family with a
positive horizon.  (`Sound31.solution_of_runPartsFamily` therefore has an empty hypothesis and
proves nothing; the repaired stroke of §3 is what the leaf needs.) -/
theorem runPartsFamily_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    ¬ Nonempty (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
        QMCLeafB.FinalStroke.RunParts o G t (P G)) := by
  rintro ⟨B⟩
  refine no_runParts_of_zero Gzero rfl (P Gzero) (hKm Gzero)
    (-(QMCLeafB.EngineRuntime.Rq Gzero / 40000) - 1) ?_ ⟨B Gzero _⟩
  have : epsG Gzero = QMCLeafB.EngineRuntime.Rq Gzero / 40000 := rfl
  rw [this]
  push_cast
  ring_nf
  norm_num

#print axioms QMCLeafB.Fam33M5.runPartsFamily_empty

/-! ## 3.  The repaired stroke: the record is needed on `2 ≤ G.n` and on the bracket only -/

/-- **`SoundεOnBracket` from a record family on `2 ≤ G.n`** — the `Sound31` stroke with the small-order
corner removed.  The proof is the same: `soundAt_of_runParts` where the graph has an edge, and
`soundAt_of_le_one` (which needs no record at all) where it does not. -/
theorem soundEpsOnBracket_of_family_le2 {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    QMCLeafB.FinishLine.SoundεOnBracket o := by
  rw [QMCLeafB.VerdictSound.soundEpsOnBracket_iff]
  intro G t hlo hhi
  by_cases hn : 2 ≤ G.n
  · exact QMCLeafB.Sound31.soundAt_of_runParts (P G) hn (B G t hn) (hKm G)
  · exact QMCLeafB.VerdictSound.soundAt_of_le_one o (by omega) t hlo hhi

#print axioms QMCLeafB.Fam33M5.soundEpsOnBracket_of_family_le2

/-- **`SoundεOnBracket` from a record family on the bracket at `2 ≤ G.n`** — the sharpest form: the
leaf's `SoundεOnBracket` is a `∀`-closure over `-Rq G ≤ t ≤ 0`, so nothing off the bracket is ever
read. -/
theorem soundEpsOnBracket_of_family_brk {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    QMCLeafB.FinishLine.SoundεOnBracket o := by
  rw [QMCLeafB.VerdictSound.soundEpsOnBracket_iff]
  intro G t hlo hhi
  by_cases hn : 2 ≤ G.n
  · exact QMCLeafB.Sound31.soundAt_of_runParts (P G) hn (B G t hn hlo hhi) (hKm G)
  · exact QMCLeafB.VerdictSound.soundAt_of_le_one o (by omega) t hlo hhi

#print axioms QMCLeafB.Fam33M5.soundEpsOnBracket_of_family_brk

/-- **The repaired closing stroke**: `SolutionStatement` from a `Poly` bit plus a record family on the
bracket at `2 ≤ G.n`. -/
theorem solution_of_runPartsFamily_le2 (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o
    (soundEpsOnBracket_of_family_le2 B hKm) ho

#print axioms QMCLeafB.Fam33M5.solution_of_runPartsFamily_le2

/-- **The repaired closing stroke on the bracket form.** -/
theorem solution_of_runPartsFamily_brk (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o
    (soundEpsOnBracket_of_family_brk B hKm) ho

#print axioms QMCLeafB.Fam33M5.solution_of_runPartsFamily_brk

/-! ## 4.  The dispatch: two residual slots, no `hE`

At a bracketed point with `2 ≤ G.n` the record is built by a single `Bool` split on the program's own
bit:

* `o G t = true` — the `M` class: a genuine unit-diagonal PSD point at `t + εr` exists (`hM`), and the
  all-`ok` stream is a record.  On the top slice `t ≥ -εr` this slot is **free** (the identity
  certifies), so `hM` is only owed on `-Rq G ≤ t < -εr`.
* `o G t = false` — either the body is empty (`RefutedM3.runParts_of_emptyBody`, all-`cut`, no side
  conditions beyond the bit) or the leftover `hC` record is owed.

There is no `hE` slot (`EmptyBody → bit = false`): the empty-body record is applied *at* the point
where the bit already reads `false`, so no implication across points is ever consumed. -/

/-- **The dispatch.** -/
noncomputable def runParts_of_cases {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = true → MemberAt G t)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (P G) → QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts o G t (P G) := by
  intro G t hn hlo hhi
  by_cases hbit : o G t = true
  · exact runParts_of_member (P G) hn (hKm G) hbit (hM G t hn hlo hhi hbit)
  · have hb : o G t = false := by
      rcases h : o G t with _ | _
      · rfl
      · exact absurd h hbit
    by_cases he : BodyEmpty G t (P G)
    · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t (P G) hn hb he
    · exact hC G t hn hlo hhi hb he

#print axioms QMCLeafB.Fam33M5.runParts_of_cases

/-- **The dispatch with `hM` only below the top slice** — `memberAt_of_neg_eps_le` frees the slot on
`t ≥ -εr`, so the member obligation lives on `[-Rq G, -εr)` only. -/
noncomputable def runParts_of_cases' {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → MemberAt G t)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (P G) → QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts o G t (P G) := by
  intro G t hn hlo hhi
  by_cases hbit : o G t = true
  · refine runParts_of_member (P G) hn (hKm G) hbit ?_
    by_cases ht : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
    · exact hM G t hn hlo ht hbit
    · exact memberAt_of_neg_eps_le G t (le_of_not_gt ht)
  · have hb : o G t = false := by
      rcases h : o G t with _ | _
      · rfl
      · exact absurd h hbit
    by_cases he : BodyEmpty G t (P G)
    · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t (P G) hn hb he
    · exact hC G t hn hlo hhi hb he

#print axioms QMCLeafB.Fam33M5.runParts_of_cases'

/-- **The leaf from two slots.**  `FinishLine.SolutionStatement` from the `Poly` bit, the member slot
on `[-Rq G, -εr)` at `2 ≤ G.n`, the leftover record slot on the bracket, and the horizon. -/
theorem solution_of_two_slots (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → MemberAt G t)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (P G) → QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_runPartsFamily_brk o P ho (runParts_of_cases' hM hC hKm) hKm

#print axioms QMCLeafB.Fam33M5.solution_of_two_slots

/-- **The programme-side obligation the family imposes**: any record family forces the bit `true` at
every bracketed point that carries a unit-diagonal PSD point strictly below the level `t - εr`
(`Sound31.bit_true_of_strict_below`).  This is a constraint on the *program*, not content of `hC`: it
says the leftover `hC` is only ever owed at points whose body has no strict-below corner (the thin
stratum). -/
theorem bit_true_of_strictBody_of_family {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t) (hhi : t ≤ 0)
    (hex : ∃ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z ∧
        (QMCLeafB.wMatrix G * Z).trace < (t : ℝ) - ((epsG G : ℚ) : ℝ)) :
    o G t = true :=
  QMCLeafB.Sound31.bit_true_of_strict_below (P G) hn (B G t hn hlo hhi) hex

#print axioms QMCLeafB.Fam33M5.bit_true_of_strictBody_of_family

/-! ## 5.  The verbatim `d9f601e5` sentence at this interface -/

/-- **The leaf's `d9f601e5` sentence**, written out, from the two slots. -/
theorem solution_fam33 (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → MemberAt G t)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (P G) → QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
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
  solution_of_two_slots o ho hM hC hKm

#print axioms QMCLeafB.Fam33M5.solution_fam33


/-! ## 6.  The repaired family is not itself vacuous — anchors at `G₀`

The original stroke died at `n = 0`; the repair must not die the same way.  Both written strata are
anchored at `G₀` (`ResidRefute.G₀`, the two-vertex one-edge input, `Rq = 1`, `wMatrix = !![0,1/2;1/2,0]`):

* the `ok` class: the rank-one point `!![1,-1;-1,1]` is unit-diagonal PSD with `tr (wMatrix G₀ · X) = -1`,
  so the bit `≡ true` satisfies `hM` on the **whole** bracket, and `runParts_of_cases` furnishes the
  family there for any parameter family;
* the `cut` class: `RefutedM3.runParts_G₀_of_bitFalse` gives a record at the bracketed point `t₀`
  where the body is empty. -/

/-- `!![1,-1;-1,1]` is unit-diagonal positive semidefinite. -/
theorem isUnitDiagPSD_X1 :
    QMCLeafB.AnswerProducer.IsUnitDiagPSD (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hpsd : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro x
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      nlinarith [sq_nonneg (x 0 - x 1)]
  refine ⟨hpsd, ?_⟩
  intro i
  fin_cases i <;> norm_num

#print axioms QMCLeafB.Fam33M5.isUnitDiagPSD_X1

/-- Its objective at `G₀` is exactly `-1` (half the off-diagonal sum). -/
theorem trace_G₀_X1 :
    (QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀ * !![1, -1; -1, 1]).trace = -1 := by
  rw [Matrix.trace, Fin.sum_univ_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two, QMCLeafB.RefutedM3.wMatrix_G₀_00,
    QMCLeafB.RefutedM3.wMatrix_G₀_11, QMCLeafB.RefutedM3.wMatrix_G₀_01,
    QMCLeafB.RefutedM3.wMatrix_G₀_10]
  norm_num

#print axioms QMCLeafB.Fam33M5.trace_G₀_X1

/-- **The member slot at `G₀` is inhabited on the whole bracket** (`t ≥ -Rq G₀ = -1`). -/
theorem memberAt_G₀ (t : ℚ) (ht : (-1 : ℝ) - 1 / 40000 ≤ (t : ℝ)) :
    MemberAt QMCLeafB.ResidRefute.G₀ t := by
  refine ⟨!![1, -1; -1, 1], isUnitDiagPSD_X1, ?_⟩
  rw [trace_G₀_X1]
  have heps : ((epsG QMCLeafB.ResidRefute.G₀ : ℚ) : ℝ) = 1 / 40000 := by
    simp [epsG, QMCLeafB.ResidRefute.Rq_G₀]
  rw [heps]
  linarith

#print axioms QMCLeafB.Fam33M5.memberAt_G₀

/-- **The `ok` stratum of the repaired family is inhabited**: at `G₀`, with the bit `≡ true`, the
dispatch builds a record at *every* bracketed `t`, for *every* parameter family.  So the repair does
not repeat the defect of §2. -/
noncomputable def anchor_ok_G₀ (P : QMCLeafB.FinalStroke.RunParams QMCLeafB.ResidRefute.G₀)
    (hKm : 0 < P.K * P.m) :
    ∀ t : ℚ, -QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts (fun _ _ => true) QMCLeafB.ResidRefute.G₀ t P := by
  intro t hlo hhi
  have h1 : (-1 : ℚ) ≤ t := by
    rw [← QMCLeafB.ResidRefute.Rq_G₀]; exact hlo
  have h2 : ((-1 : ℚ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
  push_cast at h2
  exact runParts_of_member P QMCLeafB.ResidKill.hnG₀ hKm rfl
    (memberAt_G₀ t (by linarith))

#print axioms QMCLeafB.Fam33M5.anchor_ok_G₀

/-- **The `cut` stratum of the repaired family is inhabited**: at the bracketed point `t₀` of `G₀`,
where the relaxed body is empty, every bit reading `false` carries the banked all-`cut` record. -/
theorem anchor_cut_G₀ (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hbit : o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀ = false) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o QMCLeafB.ResidRefute.G₀
      QMCLeafB.EmptyBodyM5.t₀ (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)) :=
  ⟨QMCLeafB.RefutedM3.runParts_G₀_of_bitFalse o hbit⟩

#print axioms QMCLeafB.Fam33M5.anchor_cut_G₀

/-! ## 7.  At the campaign's own parameter family

`hKm` is not a residual: `UnionShallow.one_le_Kbc2_mul` says the campaign's round count is positive.
So at `paramsKbc2` the leaf is exactly the `Poly` bit plus the two slots. -/

/-- The horizon at the campaign family. -/
theorem paramsKbc2_hKm (G : QuantumMaxCutEnergy.Input) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_K, QMCLeafB.UnionShallow.paramsKbc2_m]
  have := QMCLeafB.UnionShallow.one_le_Kbc2_mul G
  omega

#print axioms QMCLeafB.Fam33M5.paramsKbc2_hKm

/-- **The submission frame's residual is EMPTY.**  `Sub33M1.Parts33.runrec` asks for
`∀ G t, RunParts o G t (paramsKbc2 G)`; by §2 that is unsatisfiable for every bit, at the campaign's
own parameter family.  This is the receipt that the frame of the phase-33 submission file cannot be
filled as written (the repaired shape is `Parts33b` in §8). -/
theorem parts33_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
        QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :=
  runPartsFamily_empty o QMCLeafB.UnionShallow.paramsKbc2 paramsKbc2_hKm

#print axioms QMCLeafB.Fam33M5.parts33_empty

/-- **The leaf at `paramsKbc2` from the `Poly` bit and the two slots** — no numeric side condition. -/
theorem solution_campaign (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → MemberAt G t)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_two_slots o ho hM hC paramsKbc2_hKm

#print axioms QMCLeafB.Fam33M5.solution_campaign

/-- **The same at the verbatim `d9f601e5` sentence.** -/
theorem solution_campaign_verbatim (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → MemberAt G t)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
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
  solution_campaign o ho hM hC

#print axioms QMCLeafB.Fam33M5.solution_campaign_verbatim


/-! ## 8.  The repaired submission residual

`Parts33b` is the shape `Sub33M1.Parts33` takes once §2's defect is repaired: the record family is
asked for on the bracket at `2 ≤ G.n`, at the campaign's own `paramsKbc2` — the exact shape §3's
stroke consumes, so the submission frame needs no other change. -/

/-- **The submission residual, repaired.**  Three fields: the bit, its `Poly` proof, and the record
family on the bracket at `2 ≤ G.n` at the campaign parameter family. -/
structure Parts33b : Type where
  /-- the program's verdict bit -/
  o : QuantumMaxCutEnergy.Input → ℚ → Bool
  /-- the bit is computable in polynomial time -/
  hpoly : Automatic.Poly
    (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)
  /-- the run record at every bracketed point with an edge -/
  runrec : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)

/-- **Filling the three fields closes the leaf.** -/
theorem solution_of_parts33b (D : Parts33b) : QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_runPartsFamily_brk D.o QMCLeafB.UnionShallow.paramsKbc2 D.hpoly D.runrec
    paramsKbc2_hKm

#print axioms QMCLeafB.Fam33M5.solution_of_parts33b

/-- **The same, at the verbatim `d9f601e5` sentence.** -/
theorem solution_of_parts33b_verbatim (D : Parts33b) :
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
  solution_of_parts33b D

#print axioms QMCLeafB.Fam33M5.solution_of_parts33b_verbatim

/-- **What `Parts33b` owes, slot by slot** (the producer's checklist, as one theorem):
`hM` on `[-Rq G, -εr)` at bit-`true` points, `hC` at bit-`false` points with a nonempty body. -/
noncomputable def parts33b_of_slots (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hpoly : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → MemberAt G t)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    Parts33b where
  o := o
  hpoly := hpoly
  runrec := runParts_of_cases' hM hC paramsKbc2_hKm

#print axioms QMCLeafB.Fam33M5.parts33b_of_slots


/-! ## 9.  The receiving interface for the phase-33 pair (A)+(B)

The two analytic lanes of the charter plug in here, at their stated shapes:

* **(A) the rounding lemma** — a relaxed rational member at `(t - eps, dqShallow)` yields a genuine
  unit-diagonal PSD point at `t + εr`.  That is *exactly* the member slot `hM` of §4, so (A) retires
  `hM` (and with it `hok`/`Hpsd`/the grid), and the `ok` side of the leaf costs only the cheap
  relaxed-membership test `hok` of `Inst31M3` §1.
* **(B) the all-`cut` record** — the leftover `hC` slot, unchanged by (A): (A) says nothing at a point
  where the bit reads `false`, whose record must separate the whole relaxation.

Note what the assembly shows about the charter's "case (ii) absorbs case (iii)": the absorption
happens only where the *bit* reads `true`.  A bit that reads `false` at a body-nonempty point still
owes `hC`.  So (A) alone does not empty the `cut` lane; the two slots together are precisely the two
clauses of `VerdictSound.SoundAt`, which is the leaf's real residual. -/

/-- **(A) + (B) + bit ⇒ the leaf.**  `hround` is the rounding lemma at its interface shape (a relaxed
rational member at the campaign's `(level, tolerance)` gives a genuine point at `t + εr`); `hok` is
the cheap test the program's `ok` flag must satisfy; `hcut` is the all-`cut` record. -/
theorem solution_of_rounding_and_cut (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hround : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ)
      (cX : Matrix (Fin G.n) (Fin G.n) ℚ), cXᵀ = cX →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) →
      MemberAt G t)
    (hcut : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement := by
  refine solution_campaign o ho ?_ hcut
  intro G t hn hlo hhi hbit
  have hhi' : t ≤ 0 := by
    have hpos : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
      have h : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G / 40000 := by
        have := QMCLeafB.EngineRuntime.Rq_nonneg G
        linarith
      exact_mod_cast h
    have ht0 : ((t : ℚ) : ℝ) < 0 := by linarith
    exact_mod_cast le_of_lt ht0
  obtain ⟨cX, hsym, hmem⟩ := hok G t hn hlo hhi' hbit
  exact hround G t cX hsym hmem

#print axioms QMCLeafB.Fam33M5.solution_of_rounding_and_cut

/-- **The same at the verbatim `d9f601e5` sentence.** -/
theorem solution_of_rounding_and_cut_verbatim (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hround : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ)
      (cX : Matrix (Fin G.n) (Fin G.n) ℚ), cXᵀ = cX →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) →
      MemberAt G t)
    (hcut : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
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
  solution_of_rounding_and_cut o ho hok hround hcut

#print axioms QMCLeafB.Fam33M5.solution_of_rounding_and_cut_verbatim


/-! ## 10.  `hC` is only owed at the THIN stratum

`Sound31.bit_true_of_strict_below` is a *necessity* statement: at any point of the bracket that carries
a unit-diagonal PSD `Z` **strictly below** the level `t - εr`, a record forces the bit `true`.  So a
programme that has a record family at its own bit must read `true` at every such point — this is not an
extra assumption but a consequence (`bit_true_of_strictBody_of_family` above).

Consequently the leftover `hC` can be asked for only at points where **no** strict-below corner exists
while the relaxed body is nonempty — the thin stratum, the campaign's `(G₁,t₁)`-class.  That is the
sharpest place the all-`cut` lane can still be inhabited (`no_runParts_of_ball` empties the
body-nonempty stratum wherever a strict corner exists). -/

/-- A unit-diagonal PSD point strictly below the engine's level `t - εr`. -/
abbrev StrictBelow (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
    QMCLeafB.AnswerProducer.IsUnitDiagPSD Z ∧
      (QMCLeafB.wMatrix G * Z).trace < (t : ℝ) - ((epsG G : ℚ) : ℝ)

/-- **The dispatch with `hC` restricted to the thin stratum.**  `hprog` (bit `true` at strict-below
points) is the programme-side necessity; at a bit-`false` nonempty-body point it rules the strict
corner out, which is exactly `hCthin`'s missing hypothesis. -/
noncomputable def runParts_of_cases_thin {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hprog : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → StrictBelow G t → o G t = true)
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → MemberAt G t)
    (hCthin : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (P G) → ¬ StrictBelow G t →
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts o G t (P G) := by
  intro G t hn hlo hhi
  by_cases hbit : o G t = true
  · refine runParts_of_member (P G) hn (hKm G) hbit ?_
    by_cases ht : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
    · exact hM G t hn hlo ht hbit
    · exact memberAt_of_neg_eps_le G t (le_of_not_gt ht)
  · have hb : o G t = false := by
      rcases h : o G t with _ | _
      · rfl
      · exact absurd h hbit
    by_cases he : BodyEmpty G t (P G)
    · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t (P G) hn hb he
    · refine hCthin G t hn hlo hhi hb he ?_
      intro hs
      have htru := hprog G t hn hlo hhi hs
      rw [hb] at htru
      exact Bool.noConfusion htru

#print axioms QMCLeafB.Fam33M5.runParts_of_cases_thin

/-- **The leaf from the `Poly` bit and three slots**, `hC` confined to the thin stratum. -/
theorem solution_of_three_slots (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hprog : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → StrictBelow G t → o G t = true)
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → MemberAt G t)
    (hCthin : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → o G t = false →
      ¬ BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) → ¬ StrictBelow G t →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_runPartsFamily_brk o QMCLeafB.UnionShallow.paramsKbc2 ho
    (runParts_of_cases_thin hprog hM hCthin paramsKbc2_hKm) paramsKbc2_hKm

#print axioms QMCLeafB.Fam33M5.solution_of_three_slots


/-! ## 11.  `hKm` is a dead binder of the `Sound31` stroke

`soundAt_of_runParts` takes `hKm : 0 < P.K * P.m`, but the proof never reads it: the `ok` round is
extracted from `anyOk ok (P.K * P.m) = true` by `SimLoop.anyOk_eq_true_iff`, whose conclusion is
`∃ k, k < P.K * P.m ∧ ok k = true` for **every** horizon.  So the soundness clause holds at any
horizon, and the hypothesis can be dropped — verified below by a copy of the stroke's proof. -/

/-- **`SoundAt` from a record, at ANY horizon** (no `hKm`). -/
theorem soundAt_of_runParts_noKm {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (B : QMCLeafB.FinalStroke.RunParts o G t P) :
    QMCLeafB.VerdictSound.SoundAt o G t := by
  constructor
  · intro htrue
    have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = true := by
      rw [← B.hverdict]; exact htrue
    obtain ⟨k, hk, hok⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff B.ok (P.K * P.m)).1 hany
    exact B.hcert k hk hok
  · intro hfalse Z hZ
    by_contra hlt
    push Not at hlt
    have htrue := QMCLeafB.Sound31.bit_true_of_strict_below P hn B ⟨Z, hZ, hlt⟩
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue

#print axioms QMCLeafB.Fam33M5.soundAt_of_runParts_noKm

/-- The `hKm`-free closing stroke, on the repaired family. -/
theorem solution_of_runPartsFamily_noKm (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts o G t (P G)) :
    QMCLeafB.FinishLine.SolutionStatement := by
  refine QMCLeafB.FinishLine.solution_of_bracket_verdict o ?_ ho
  rw [QMCLeafB.VerdictSound.soundEpsOnBracket_iff]
  intro G t hlo hhi
  by_cases hn : 2 ≤ G.n
  · exact soundAt_of_runParts_noKm (P G) hn (B G t hn hlo hhi)
  · exact QMCLeafB.VerdictSound.soundAt_of_le_one o (by omega) t hlo hhi

#print axioms QMCLeafB.Fam33M5.solution_of_runPartsFamily_noKm

/-! **What this does and does not buy.**  It removes `hKm` from the residual — the family is asked for
at any horizon — so §2's defect cannot be blamed on the positivity condition (`n = 0` with `K·m = 0`
would be a record family only for bits reading `false` everywhere at that input, which the bracket
stroke would then have to be sound for; it is not).  The `2 ≤ G.n` restriction remains necessary. -/


end QMCLeafB.Fam33M5


