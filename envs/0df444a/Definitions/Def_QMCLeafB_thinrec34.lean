-- Prove2me | Definitions.Def_QMCLeafB_thinrec34
-- name    : QMCLeafB_thinrec34
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:16:55.316729+00:00
-- url     : https://prove2.me/theorems/78ec4c63-dbc9-414d-8491-4265fb0a9a95
-- title:
--   QMCLeafB thinrec34
-- statement:
--   # `Check_thinrec34_m4` — the thin stratum's record: decided, reduced to ONE obligation
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_answer_producer
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_runparts_dilate_m5
import Definitions.Def_QMCLeafB_refuted_m3
/-
# `Check_thinrec34_m4` — the thin stratum's record: decided, reduced to ONE obligation

Phase 34, member m4, direction d5 (`thin-record`).  The leaf at the phase-33 interface is

    `hok`     : `o G t = true`  ⟹ ∃ symmetric rational `RelaxMem` at `(t - eps, dqShallow)`
    `hfalse`  : `o G t = false` ⟹ `RunParts o G t (P G)`

and the phase-32/33 harvest retires the exact-diagonal program, replaces its `ok` test by the
released gate `dvR s ≤ dqOf s / 4`, and leaves `hfalse` owed exactly at bit-`false` points with a
NONEMPTY relaxed body.  This file settles what that duty is.

## The answer to the direction's question

**The all-false record class is PROGRAM-FREE.**  `RunParts.hverdict` is
`o G t = anyOk ok (K·m)`; at a bit-`false` point `anyOk_eq_false_iff` turns it into `ok ≡ false`,
after which the bit appears in no field.  So the duty at a bit-`false` point is *exactly*
`BodyRec G t P` := `Nonempty (RunParts (fun _ _ => false) G t P)` — see `runParts_false_iff_bodyRec`
(§1).  Consequence, machine-checked: **"change the program so the bit reads true there" is not a
cheaper alternative to building the record** — the record class does not depend on the program at
all.  The only program change that removes the duty is making the bit read `true`, and that is
*exactly* `hcomplete` on the thin stratum: the other open slot, not an escape from it.  At EMPTY
bodies the duty is already discharged by the banked `RefutedM3.runParts_of_emptyBody` (§4), so
`hfalse` is owed only at bit-`false` NONEMPTY points.

**The record has six free slots and one real one.**  Given ANY nonzero rational normal stream `c`,
`RunPartsDilate.runCut` produces a transcript whose engine slots `hwit`/`hrho`/`hcne`/`hle` all
hold with `ρ ≡ rmax` (the largest legal normalised depth), and `hcheck` is then the *rational* check
`(del k)² ≤ rmax²·σ_k` (§3, `slots_of_normals`).  So six of `allFalseParts`' seven slots cost a
choice of normals; the seventh is `hcut`.

**`hcut` is one inequality per round** (§2 necessary, §3 sufficient):
`BodyRec` follows from, and every record forces, a nonzero normal stream with rational margins
`del` such that `del k ≥ max_{z ∈ relaxBall} (c_k·Cat k − c_k·z)` and `(del k)² ≤ rmax²·σ_k`.  Call
it `ShallowCut` (§5).  In words: *at every round the accumulated engine centre `Cat k` must be
within the round's margin of a supporting hyperplane of the WHOLE relaxation, and that margin is
capped at `ρ_k·√σ_k ≤ rmax·√σ_k`.*  `encl_of_bodyRec` proves it necessary for any record;
`bodyRec_of_shallow` proves a normal stream plus margins with it sufficient.  That is the single
open obligation of the thin stratum, and it is a *trajectory* obligation, not a body condition —
which is why the banked volume/cube obstructions (`BallM2.no_runParts_of_ball`,
`AlcutM3.no_cube_of_allFalse`) give nothing on the thin band: they need ball/cube content that a
thin body does not have.

## What is proved here (all machine-checked, axioms audited)

* §1 `runParts_false_iff_bodyRec`, `hfalse_iff_bodyRec` — the program-free reduction.
* §2 `encl_of_bodyRec` — every all-false record forces the shallow-cut inequality at every round
  (NECESSARY).
* §3 `slots_of_normals`, `bodyRec_of_shallow` — `runCut` at any nonzero normal stream supplies the
  six engine slots, and the shallow-cut inequality plus the rational margin check supplies the
  record (SUFFICIENT).
* §4 `bodyRec_of_emptyBody` — the empty stratum is FREE (banked `runParts_of_emptyBody`), so the
  duty is confined to nonempty bodies.
* §5 `ShallowCut`, `bodyRec_of_shallowCut`, `hfalse_thin_residual`, `hfalse_of_shallowCut`,
  `hfalse_of_bit_complete`, `hfalse_family_of_shallowCut`, `hfalse_family_of_bit_complete` — the
  residual in the leaf's own terms, at an arbitrary bit `o`, both horns.
* §6 `not_bodyRec_of_ball` — ball-bearing bodies admit NO all-false record (banked
  `BallM2.no_runParts_of_ball`), so the duty is exactly the ball-free strictly-thin stratum.
* §7 `RecordDatum`, `bodyRec_iff_recordDatum`, `shallowCut_to_recordDatum` — the EXACT two-sided
  characterisation: `BodyRec ⟺ RecordDatum`, a program-free horizon-guarded satisfaction problem,
  whose canonical witness is `ShallowCut`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every theorem.  Imports: `Mathlib` + published `Definitions.Def_QMCLeafB_*`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ThinRec34M4

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates

/-- The constant-`false` bit.  `RunParts` at this bit is the ALL-FALSE record class: every round is
a cut round, so `hcert` is vacuous and `hverdict` reads `false = false`. -/
abbrev falseBit : QuantumMaxCutEnergy.Input → ℚ → Bool := fun _ _ => false

/-- **The all-false record class at `(G,t)`**, as a program-free predicate: it says nothing about
any candidate verdict bit. -/
def BodyRec (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  Nonempty (QMCLeafB.FinalStroke.RunParts falseBit G t P)

/-- The relaxed body at `P`'s tolerance is empty (the hypothesis `runParts_of_emptyBody` eats). -/
def BodyEmpty (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
      ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ) X

/-- The relaxation the record's `hcut` quantifies over, at `P`'s tolerance. -/
def relaxBallP (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Set (Fin (G.n * G.n) → ℝ) :=
  QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
    ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ)
    (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)

/-- The engine's initial shape at `P` is `RunParts.hwit`'s own shape (both are
`initShapeOf (n·n) (2n² + 2dq²)`, definitionally). -/
theorem initShape_eq (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) :
    QMCLeafB.RunPartsDilate.A0P G P
      = QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2) := rfl

#print axioms QMCLeafB.ThinRec34M4.initShape_eq

/-- `anyOk` of a constant-`false` stream is `false`. -/
theorem anyOk_const_false : ∀ T : ℕ,
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => false) T = false
  | 0 => rfl
  | (k + 1) => by
      rw [QMCLeafB.SimLoop.anyOk_succ, anyOk_const_false k]
      rfl

#print axioms QMCLeafB.ThinRec34M4.anyOk_const_false

/-! ## 1.  The all-false class is PROGRAM-FREE

`RunParts.hverdict` is the only field that mentions the bit `o`.  At a bit-`false` point it is the
equation `false = anyOk ok (K·m)`, which `SimLoop.anyOk_eq_false_iff` turns into `ok ≡ false`; after
that the word "bit" does not occur.  Both directions are field-by-field rebuilding, so this is a
statement about the STRUCTURE and costs nothing analytic. -/

/-- **The reduction.**  At a bit-`false` point, a record for the program's bit and an all-false
record are the same object. -/
theorem runParts_false_iff_bodyRec {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (h : o G t = false) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o G t P) ↔ BodyRec G t P := by
  constructor
  · rintro ⟨B⟩
    have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = false := by
      rw [← B.hverdict]; exact h
    refine ⟨{ ok := B.ok, cd := B.cd, del := B.del,
              hcert := B.hcert, hwit := B.hwit, hrho := B.hrho, hcne := B.hcne,
              hdel0 := B.hdel0, hcheck := B.hcheck, hle := B.hle, hcut := B.hcut,
              hverdict := ?_ }⟩
    show (false : Bool) = QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m)
    rw [hany]
  · rintro ⟨B⟩
    have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = false := B.hverdict.symm
    refine ⟨{ ok := B.ok, cd := B.cd, del := B.del,
              hcert := B.hcert, hwit := B.hwit, hrho := B.hrho, hcne := B.hcne,
              hdel0 := B.hdel0, hcheck := B.hcheck, hle := B.hle, hcut := B.hcut,
              hverdict := ?_ }⟩
    show o G t = QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m)
    rw [h, hany]

#print axioms QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec

/-- **`hfalse` is program-free at every bit-`false` point.** -/
theorem hfalse_iff_bodyRec {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (h : o G t = false) :
    (o G t = false → Nonempty (QMCLeafB.FinalStroke.RunParts o G t P)) ↔ BodyRec G t P := by
  constructor
  · intro H; exact (runParts_false_iff_bodyRec h).1 (H h)
  · intro H _; exact (runParts_false_iff_bodyRec h).2 H

#print axioms QMCLeafB.ThinRec34M4.hfalse_iff_bodyRec

/-! ## 2.  NECESSARY: every all-false record forces the shallow-cut inequality

At round `k` the record's own `hcut` says the whole relaxation lies above the hyperplane through
`Cat k` at margin `del k` in the direction `c_k`, and `hcheck`+`hle` cap that margin at
`ρ_k·√σ_k ≤ rmax·√σ_k`.  Composing: the accumulated engine centre is within `rmax·√σ_k` of a
supporting hyperplane of the relaxation, in the direction `c_k`.  This is what a *shallow* cut
means, and it is the one thing the record has to deliver at every round. -/


/-- **The recorded margin never exceeds `rmax·√σ`** — with NO positivity hypothesis on `σ`.  Both
cases close: `σ ≥ 0` is `margin_le_of_sq_check`, and `σ < 0` forces `del = 0` (since `ρ²σ ≤ 0`) and
`Real.sqrt σ = 0`. -/
theorem del_le_rmax_sqrt {n : ℕ} {c p : Fin n → ℚ} {rmax ρ del : ℚ}
    (hrmax : 0 ≤ rmax) (hrho : 0 ≤ ρ) (hle : ρ ≤ rmax) (hdel0 : 0 ≤ del)
    (hchk : del ^ 2 ≤ ρ ^ 2 * QMCLeafB.EngineIterates.sigmaQ c p) :
    (del : ℝ) ≤ (rmax : ℝ)
      * Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ c p : ℚ)) : ℝ) := by
  by_cases hσ : (0 : ℚ) ≤ QMCLeafB.EngineIterates.sigmaQ c p
  · have hρ2 : ρ ^ 2 ≤ rmax ^ 2 := by nlinarith
    have h1 : del ^ 2 ≤ rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ c p := by
      have := hchk
      nlinarith
    exact QMCLeafB.EngineIterates.margin_le_of_sq_check hdel0 hrmax hσ h1
  · rw [not_le] at hσ
    have h1 : ρ ^ 2 * QMCLeafB.EngineIterates.sigmaQ c p ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ρ) hσ.le
    have h2 : del ^ 2 ≤ 0 := le_trans hchk h1
    have h3 : del = 0 := by nlinarith [sq_nonneg del]
    rw [h3]
    have hcast : (0 : ℝ) ≤ (rmax : ℝ) := by exact_mod_cast hrmax
    have hsq : (0 : ℝ) ≤ Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ c p : ℚ)) : ℝ) :=
      Real.sqrt_nonneg _
    have := mul_nonneg hcast hsq
    simpa using this

#print axioms QMCLeafB.ThinRec34M4.del_le_rmax_sqrt

/-- **NECESSARY half of the characterisation.**  Any all-false record satisfies the shallow-cut
inequality at every round below the horizon: the accumulated centre `Cat k` is at most `del k` above
the relaxation's supporting level in the direction `c_k`, and `del k ≤ rmax·√σ_k`. -/
theorem encl_of_bodyRec {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts falseBit G t P) :
    ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      QMCLeafB.EngineIterates.cutCR B.cd k
          ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k
        - QMCLeafB.EngineIterates.cutCR B.cd k ⬝ᵥ z
        ≤ (P.rmax : ℝ)
          * Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ (B.cd k).c (B.cd k).p : ℚ)) : ℝ) := by
  intro k hk z hz
  have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = false := B.hverdict.symm
  have hok : B.ok k = false :=
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).1 hany k hk
  have hcut := B.hcut k hk hok z hz
  have hchk := B.hcheck k hk hok
  have hrho := B.hrho k hk hok
  have hle := B.hle k hk hok
  have hbound : ((B.del k : ℚ) : ℝ) ≤ (P.rmax : ℝ)
      * Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ (B.cd k).c (B.cd k).p : ℚ)) : ℝ) :=
    del_le_rmax_sqrt P.hrmax hrho hle (B.hdel0 k hk hok) hchk
  rw [dotProduct_sub] at hcut
  linarith

#print axioms QMCLeafB.ThinRec34M4.encl_of_bodyRec

/-! ## 3.  SUFFICIENT: six free slots, one real one

`RunPartsDilate.runCut` turns ANY nonzero rational normal stream into a transcript with
`p_k = A_k⁻¹ c_k` (its `runCut_wit`), `ρ_k ≡ rmax` (maximal legal depth), and the `hwit` shape is
`RunParts`' own.  So `hwit`, `hrho`, `hcne`, `hle` cost nothing but a choice of normals; `hcheck` is
then the rational comparison `(del k)² ≤ rmax²·σ_k`; `hcut` is the shallow-cut inequality. -/

/-- The transcript carried by a nonzero normal stream. -/
def NormalCut (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  QMCLeafB.RunPartsDilate.runCut G P hn c hc

/-- **Six of the seven slots are free.**  For any nonzero normal stream the transcript `NormalCut`
satisfies `hwit`, `hrho`, `hcne`, `hle`; `hcheck` holds whenever the recorded margins satisfy the
rational check `del k² ≤ rmax²·σ_k`. -/
theorem slots_of_normals {G : QuantumMaxCutEnergy.Input}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (del : ℕ → ℚ)
    (hdel : ∀ k, (del k) ^ 2
      ≤ P.rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ (c k)
          ((NormalCut G P hn c hc k).p)) :
    (∀ k, QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) (NormalCut G P hn c hc) k
        *ᵥ ((NormalCut G P hn c hc k).p)
      = (NormalCut G P hn c hc k).c)
    ∧ (∀ k, (NormalCut G P hn c hc k).rho = P.rmax)
    ∧ (∀ k, (NormalCut G P hn c hc k).c = c k)
    ∧ (∀ k, (NormalCut G P hn c hc k).c ≠ 0)
    ∧ (∀ k, (del k) ^ 2
      ≤ (NormalCut G P hn c hc k).rho ^ 2
          * QMCLeafB.EngineIterates.sigmaQ (NormalCut G P hn c hc k).c
              (NormalCut G P hn c hc k).p) := by
  have hwit : ∀ k, QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) (NormalCut G P hn c hc) k
      *ᵥ ((NormalCut G P hn c hc k).p) = (NormalCut G P hn c hc k).c := by
    intro k
    have h := QMCLeafB.RunPartsDilate.runCut_wit G P hn c hc k
    rw [← initShape_eq G P]
    exact h
  refine ⟨hwit, fun k => rfl, fun k => rfl, fun k => hc k, ?_⟩
  intro k
  have hc' : (NormalCut G P hn c hc k).c = c k := rfl
  have hr' : (NormalCut G P hn c hc k).rho = P.rmax := rfl
  rw [hc', hr']
  exact hdel k

#print axioms QMCLeafB.ThinRec34M4.slots_of_normals

/-- **SUFFICIENT half.**  A nonzero normal stream plus rational margins obeying the shallow-cut
inequality and the rational depth check produce the all-false record. -/
theorem bodyRec_of_shallow {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (del : ℕ → ℚ)
    (hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k)
    (hdel : ∀ k, (del k) ^ 2
      ≤ P.rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ (c k)
          ((NormalCut G P hn c hc k).p))
    (hshallow : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k
          ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (NormalCut G P hn c hc) k
        - QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k ⬝ᵥ z
        ≤ ((del k : ℚ) : ℝ)) :
    BodyRec G t P := by
  obtain ⟨hwit, hrho, hcdc, hcne, hchk⟩ := slots_of_normals hn c hc del hdel
  refine ⟨{ ok := fun _ => false
            cd := NormalCut G P hn c hc
            del := del
            hcert := ?_
            hwit := ?_
            hrho := ?_
            hcne := ?_
            hdel0 := ?_
            hcheck := ?_
            hle := ?_
            hcut := ?_
            hverdict := ?_ }⟩
  · intro k hk hok
    exact absurd hok (by simp)
  · intro k hk hok
    exact hwit k
  · intro k hk hok
    rw [hrho k]; exact P.hrmax
  · intro k hk hok
    exact hcne k
  · intro k hk hok
    exact hdel0 k hk
  · intro k hk hok
    exact hchk k
  · intro k hk hok
    rw [hrho k]
  · intro k hk hok z hz
    have h := hshallow k hk z hz
    rw [dotProduct_sub]
    linarith
  · show (false : Bool) = QMCLeafB.SimLoop.anyOk (fun _ => false) (P.K * P.m)
    exact (anyOk_const_false (P.K * P.m)).symm

#print axioms QMCLeafB.ThinRec34M4.bodyRec_of_shallow

/-! ## 4.  The empty stratum is free

At an empty relaxed body the record's `hcut` is vacuous, and the banked
`RefutedM3.runParts_of_emptyBody` already produces one — at the constant-`false` bit too, by §1.  So
`BodyRec` holds there and the duty is confined to NONEMPTY bodies. -/

/-- **The empty stratum costs nothing** — `BodyRec` is inhabited by the banked construction. -/
theorem bodyRec_of_emptyBody {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (hempty : BodyEmpty G t P) :
    BodyRec G t P :=
  ⟨QMCLeafB.RefutedM3.runParts_of_emptyBody G t P hn rfl hempty⟩

#print axioms QMCLeafB.ThinRec34M4.bodyRec_of_emptyBody

/-! ## 5.  The residual, in the leaf's own terms -/

/-- **`ShallowCut`** — the whole content of the thin stratum's record, as one predicate: a nonzero
normal stream and rational margins whose depth check is affordable and whose accumulated centre
stays within the margin of a supporting hyperplane of the relaxation at every round. -/
def ShallowCut (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Prop :=
  ∃ (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (del : ℕ → ℚ),
    (∀ k, k < P.K * P.m → 0 ≤ del k)
    ∧ (∀ k, (del k) ^ 2 ≤ P.rmax ^ 2
        * QMCLeafB.EngineIterates.sigmaQ (c k) ((NormalCut G P hn c hc k).p))
    ∧ (∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
        QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k
            ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
                (NormalCut G P hn c hc) k
          - QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k ⬝ᵥ z
          ≤ ((del k : ℚ) : ℝ))

/-- **`BodyRec` ⟸ `ShallowCut`** (the direction the record prover needs). -/
theorem bodyRec_of_shallowCut {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (H : ShallowCut G t P hn) : BodyRec G t P := by
  obtain ⟨c, hc, del, hdel0, hdel, hshallow⟩ := H
  exact bodyRec_of_shallow hn c hc del hdel0 hdel hshallow

#print axioms QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut

/-- **The thin stratum's residual, stated exactly.**  At `2 ≤ n` and a bit-`false` point, `hfalse`
holds iff the program-free record class is inhabited. -/
theorem hfalse_thin_residual {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (h : o G t = false) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o G t P) ↔ BodyRec G t P :=
  runParts_false_iff_bodyRec h

#print axioms QMCLeafB.ThinRec34M4.hfalse_thin_residual

/-- **The duty is confined to nonempty bodies.**  At an empty body the record is free. -/
theorem bodyRec_or_empty {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) :
    BodyEmpty G t P → BodyRec G t P :=
  bodyRec_of_emptyBody hn

#print axioms QMCLeafB.ThinRec34M4.bodyRec_or_empty


/-- **The duty at a bit-`false` point is `BodyEmpty ∨ BodyRec`** — the exact split of the thin
stratum.  Everything else (the empty branch) is banked. -/
noncomputable def hfalse_of_empty_or_rec {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n)
    (h : o G t = false → (BodyEmpty G t P ∨ BodyRec G t P)) :
    o G t = false → QMCLeafB.FinalStroke.RunParts o G t P := by
  intro hbit
  by_cases he : BodyEmpty G t P
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t P hn hbit he
  · exact Classical.choice ((runParts_false_iff_bodyRec hbit).2
      ((h hbit).resolve_left he))

#print axioms QMCLeafB.ThinRec34M4.hfalse_of_empty_or_rec

/-- **HORN 1 (build the record).**  `hfalse` at a bit-`false` point follows from the shallow-cut
witness there.  No emptiness case analysis, no program hypothesis. -/
noncomputable def hfalse_of_shallowCut {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (H : o G t = false → ShallowCut G t P hn) :
    o G t = false → QMCLeafB.FinalStroke.RunParts o G t P := by
  intro hbit
  exact Classical.choice ((runParts_false_iff_bodyRec hbit).2
    (bodyRec_of_shallowCut hn (H hbit)))

#print axioms QMCLeafB.ThinRec34M4.hfalse_of_shallowCut

/-- **HORN 2 (change the program).**  If the bit reads `true` at every point with a NONEMPTY body,
`hfalse` holds at that point with NO record and NO trajectory content — the banked
`runParts_of_emptyBody` covers the only remaining case.  This is the exact form of the "make the bit
read true there" repair, and it is `hcomplete` on the thin stratum: nothing weaker closes this
branch, and by §1 nothing at all closes the other branch except a shallow-cut trajectory. -/
noncomputable def hfalse_of_bit_complete {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (hcmp : ¬ BodyEmpty G t P → o G t = true) :
    o G t = false → QMCLeafB.FinalStroke.RunParts o G t P := by
  intro hbit
  by_cases he : BodyEmpty G t P
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t P hn hbit he
  · exact absurd hbit (by rw [hcmp he]; simp)

#print axioms QMCLeafB.ThinRec34M4.hfalse_of_bit_complete

/-- **THE LEAF'S `hfalse`, REDUCED.**  This is the exact shape `PBit33M6.Hd33_of_relaxMem` consumes:
`hfalse : ∀ G t, 2 ≤ n → (-Rq ≤ t) → (t : ℝ) < -Rq/40000 → o G t = false → RunParts o G t (P G)`.
It follows from `ShallowCut` at every bit-`false` point of the bracket, and from nothing else in this
file (the emptiness branch is inside the proof). -/
noncomputable def hfalse_family_of_shallowCut
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (H : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      o G t = false → ShallowCut G t (P G) hn) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      o G t = false → QMCLeafB.FinalStroke.RunParts o G t (P G) := by
  intro G t hn hbit
  exact Classical.choice ((runParts_false_iff_bodyRec hbit).2
    (bodyRec_of_shallowCut hn (H G t hn hbit)))

#print axioms QMCLeafB.ThinRec34M4.hfalse_family_of_shallowCut

/-- **THE LEAF'S `hfalse`, REDUCED (horn 2).**  Same statement, from the bit reading `true` wherever
the body is nonempty. -/
noncomputable def hfalse_family_of_bit_complete
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (H : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      ¬ BodyEmpty G t (P G) → o G t = true) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      o G t = false → QMCLeafB.FinalStroke.RunParts o G t (P G) := by
  intro G t hn hbit
  exact Classical.choice ((runParts_false_iff_bodyRec hbit).2
    (bodyRec_of_emptyBody hn (by
      by_contra hne
      exact absurd hbit (by rw [H G t hn hne]; simp))))

#print axioms QMCLeafB.ThinRec34M4.hfalse_family_of_bit_complete


/-! ## 6.  The stratum boundary is machine-checked: ball-bearing bodies admit NO record

The banked volume obstruction `BallM2.no_runParts_of_ball` says any `RunParts` at a body bearing the
campaign ball forces the bit `true`.  At the constant-`false` bit that is a contradiction, so
`BodyRec` is EMPTY there.  Together with §5 this settles the shape of the remaining work:

* ball-bearing (fat) bodies — `BodyRec` empty, so `hfalse` is IMPOSSIBLE; the released-gate program
  must read `true` there (direction 3's obligation);
* ball-free (strictly thin) bodies — the record is owed, and §5 says which one. -/

/-- **No all-false record at a ball-bearing body.** -/
theorem not_bodyRec_of_ball {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P) :
    ¬ BodyRec G t P := by
  rintro ⟨B⟩
  have h := QMCLeafB.BallM2.no_runParts_of_ball hn hball B
  exact Bool.false_ne_true (show (false : Bool) = true from h)

#print axioms QMCLeafB.ThinRec34M4.not_bodyRec_of_ball


/-! ## 7.  The exact two-sided characterisation

`encl_of_bodyRec` is the necessary half and `bodyRec_of_shallow` the sufficient half; this section
packs them as ONE equivalence.  `RecordDatum` is the record's engine-and-cut content with the bit
removed and every slot horizon-guarded exactly as `RunParts` guards it.  Then

    `BodyRec G t P  ⟺  RecordDatum G t P`,

and the canonical witness of the right-hand side is the `runCut` transcript at any nonzero normal
stream with margins obeying the shallow-cut inequality (`shallowCut_to_recordDatum`).  So the thin
stratum owes exactly one object: the shallow-cut datum.  Nothing about the program, nothing about
the size ledger, nothing about the ok test. -/

/-- **The record's content, bit-free and horizon-guarded**, in `RunParts`' own slot shapes. -/
def RecordDatum (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∃ (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ),
    (∀ k, k < P.K * P.m → QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k *ᵥ (cd k).p = (cd k).c)
    ∧ (∀ k, k < P.K * P.m → 0 ≤ (cd k).rho)
    ∧ (∀ k, k < P.K * P.m → (cd k).rho ≤ P.rmax)
    ∧ (∀ k, k < P.K * P.m → (cd k).c ≠ 0)
    ∧ (∀ k, k < P.K * P.m → 0 ≤ del k)
    ∧ (∀ k, k < P.K * P.m → (del k) ^ 2
        ≤ (cd k).rho ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    ∧ (∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
        QMCLeafB.EngineIterates.cutCR cd k
            ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
          - QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ z ≤ ((del k : ℚ) : ℝ))

/-- **`RecordDatum` ⟹ `BodyRec`** (build the record). -/
theorem bodyRec_of_recordDatum {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (H : RecordDatum G t P) : BodyRec G t P := by
  obtain ⟨cd, del, hwit, hrho, hle, hcne, hdel0, hcheck, hcut⟩ := H
  exact ⟨{ ok := fun _ => false
           cd := cd
           del := del
           hcert := by intro k hk hok; exact absurd hok (by simp)
           hwit := by intro k hk _; exact hwit k hk
           hrho := by intro k hk _; exact hrho k hk
           hcne := by intro k hk _; exact hcne k hk
           hdel0 := by intro k hk _; exact hdel0 k hk
           hcheck := by intro k hk _; exact hcheck k hk
           hle := by intro k hk _; exact hle k hk
           hcut := by
             intro k hk _ z hz
             have h := hcut k hk z hz
             rw [dotProduct_sub]
             linarith
           hverdict := (anyOk_const_false (P.K * P.m)).symm }⟩

#print axioms QMCLeafB.ThinRec34M4.bodyRec_of_recordDatum

/-- **`BodyRec` ⟹ `RecordDatum`** (read off the record's own data — this is the NECESSARY half). -/
theorem recordDatum_of_bodyRec {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (B : QMCLeafB.FinalStroke.RunParts falseBit G t P) :
    RecordDatum G t P := by
  have hall : ∀ k, k < P.K * P.m → B.ok k = false :=
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).1 B.hverdict.symm
  exact ⟨B.cd, B.del,
    fun k hk => B.hwit k hk (hall k hk),
    fun k hk => B.hrho k hk (hall k hk),
    fun k hk => B.hle k hk (hall k hk),
    fun k hk => B.hcne k hk (hall k hk),
    fun k hk => B.hdel0 k hk (hall k hk),
    fun k hk => B.hcheck k hk (hall k hk),
    fun k hk z hz => by
      have h := B.hcut k hk (hall k hk) z hz
      rw [dotProduct_sub] at h
      linarith⟩

#print axioms QMCLeafB.ThinRec34M4.recordDatum_of_bodyRec

/-- **THE CHARACTERISATION.**  The thin stratum's record duty is exactly `RecordDatum` — a
program-free, horizon-guarded, bit-free satisfaction problem. -/
theorem bodyRec_iff_recordDatum {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} :
    BodyRec G t P ↔ RecordDatum G t P := by
  constructor
  · rintro ⟨B⟩; exact recordDatum_of_bodyRec B
  · exact bodyRec_of_recordDatum

#print axioms QMCLeafB.ThinRec34M4.bodyRec_iff_recordDatum

/-- **`ShallowCut` supplies `RecordDatum`** — the canonical witness: the `runCut` transcript at a
nonzero normal stream, `ρ ≡ rmax`, margins from the rational depth check.  So a record prover only
has to produce `ShallowCut`, and `RecordDatum`/`BodyRec` follow. -/
theorem shallowCut_to_recordDatum {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (H : ShallowCut G t P hn) : RecordDatum G t P := by
  obtain ⟨c, hc, del, hdel0, hdel, hshallow⟩ := H
  obtain ⟨hwit, hrho, hcdc, hcne, hchk⟩ := slots_of_normals hn c hc del hdel
  refine ⟨NormalCut G P hn c hc, del, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _
    exact hwit k
  · intro k _
    rw [hrho k]; exact P.hrmax
  · intro k _
    rw [hrho k]
  · intro k _
    exact hcne k
  · intro k hk
    exact hdel0 k hk
  · intro k _
    exact hchk k
  · intro k hk
    exact hshallow k hk

#print axioms QMCLeafB.ThinRec34M4.shallowCut_to_recordDatum

end QMCLeafB.ThinRec34M4


