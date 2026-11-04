-- Prove2me | Definitions.Def_QMCLeafB_brick_finish_line
-- name    : QMCLeafB_brick_finish_line
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:17:27.856147+00:00
-- url     : https://prove2.me/theorems/2ded2f36-2243-4f17-8f23-fea8778c54e2
-- title:
--   QMCLeafB brick_finish_line
-- statement:
--   # leaf B phase 6 — brick `finish-line` (swarm `smvzyocty`, member m7, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_SlackRoute_m2
import Definitions.Def_QMCLeafB_brick_rq_program
/-
# leaf B phase 6 — brick `finish-line` (swarm `smvzyocty`, member m7, direction d3)

`d9f601e5` (`QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2`) from the slack route, with
every bookkeeping slot discharged and the remaining obligation reduced to **one** `Poly`
statement.

What is in this file:

* `SolutionStatement` — the campaign's sentence, written out token for token from the problem
  statement (`Definitions/Def_QuantumMaxCutFiniteNumericRuntime` + the inline `Matrix.of`), plus
  `solutionStatement_iff_wMatrix : SolutionStatement ↔ (the `wMatrix` form)` proved by `Iff.rfl`,
  which is what makes the closing theorems of `Solutions/Check_SlackRoute_m2.lean` applicable by
  `exact`;
* `solution_of_eng` — the direct stroke: `QMCLeafB.SlackRoute.leafB_of_slack_verdict` with
  `o := fun G t => sbit (eng G) t`, so the agreement hypothesis `hag` is `rfl`, and `hR` is
  `QMCLeafB.BrickRQ.Rq_poly`;
* `Soundε`, `engineOfε`, `sbit_engineOfε` — the slack analogue of `Check_BitProgram_m3`'s
  `Sound`/`engineOf`/`answerBit_engineOf`: a *verdict* Boolean, its two-sided certificate
  contract at the leaf's own slacks `εw = εr = Rq G/40000`, the engine it induces, and the proof
  that the induced engine's `sbit` **is** the verdict.  So a sound verdict needs no `hag`;
* `solution_of_ho` — the residual of the whole campaign on this route: **one** `Poly` program for
  a sound verdict bit, nothing else;
* `solution_of_program` — the same with the program handed in as an arbitrary function `sim`
  together with pointwise agreement with the verdict, so a simulation program can be dropped in
  without restating the `Poly` goal;
* §5 the arithmetic of the two slacks: `Rq/40000 + Rq/40000 = W/10000 ≤ W/7500`;
* §6 **the bracket clamp** — an ellipsoid run only certifies thresholds in `[-Rq G, 0]`, while
  `Soundε` is total in `t`; `SoundεOnBracket`, `clampBit`, `soundε_clampBit` and `poly_clampBit`
  remove the mismatch, and `solution_of_bracket_verdict` / `solution_of_bracket_program` are the
  forms the loop bricks should target;
* §7 `soundε_truthBit`, `exists_soundε` — the specification is inhabited by the classical truth,
  so the residual is computability and nothing else; `solution_of_exists_sound{,_bracket}` state
  the leaf as one existential over programs;
* §8 axiom audit.

RECOMMENDED CONSUMER for the loop bricks (d1/d2):

    exact QMCLeafB.FinishLine.solution_of_bracket_program o hsound sim hspec hprog

i.e. prove `SoundεOnBracket o` (soundness of both verdict branches on `-Rq G ≤ t ≤ 0`) and
`Automatic.Poly sim` with `∀ p, sim p = o p.1.1 p.2`; nothing else is outstanding.

No `sorry`, no `axiom`; the audit shows the standard three.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.FinishLine

open QuantumMaxCutEnergy
open QMCLeafB.EngineRuntime

/-! ## 1.  The sentence of `d9f601e5`, verbatim -/

/-- **`QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2`** (theorem id
`d9f601e5-8c68-4369-a27d-701e73e686b8`), copied token for token from the problem statement. -/
def SolutionStatement : Prop :=
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
      S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000

/-- **The written-out matrix is `QMCLeafB.wMatrix`.**  `QMCLeafB.wMatrix` is *defined* as that
`Matrix.of`, so the two formulations of the sentence are the same proposition, and every closing
theorem stated over `wMatrix` closes a goal stated with the inline matrix by `exact`.  This
lemma is the machine check of that claim. -/
theorem solutionStatement_iff_wMatrix :
    SolutionStatement ↔
      ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
        Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
          QuantumMaxCutEnergy.encodeValue
          (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
        ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
          ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
          (L G : ℝ) ≤ S ∧
          S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  Iff.rfl

/-- The request coding the leaf's `TM2`/`Poly` statements use, spelt as `⟨encodeRequest⟩`
exactly as `QMCLeafB.EngineRuntime` and `QMCLeafB.BrickRQ` do. -/
local instance instRequestCoding : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 2.  The direct stroke: the engine plus one program for its verdict

`QMCLeafB.SlackRoute.leafB_of_slack_verdict` asks for four things.  Two are already compiled
(`hR` from `brick-rq-program`, the whole value/bisection/sandwich layer inside that theorem), one
is `rfl` if the verdict is *defined* as the engine's own bit, and the fourth is the program. -/

/-- **`d9f601e5` from a slack engine and one program for its verdict bit.**

* `eng` — the per-graph engine at the leaf's slacks `εw = εr = Rq G/40000` (the mathematics of
  the ellipsoid loop: a witness up to `Rq/40000` or a refutation down to `Rq/40000`);
* `ho` — **the only computation**: a polynomial-time program that, on the encoded request
  (graph, random tape, rational threshold), returns the verdict bit of that engine.

No exact SDP-feasibility decision is asked for anywhere. -/
theorem solution_of_eng
    (eng : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.AnswerProducer.Answerε (QMCLeafB.wMatrix G) t (Rq G / 40000) (Rq G / 40000))
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QMCLeafB.SlackRoute.sbit (eng p.1.1) p.2)) :
    SolutionStatement :=
  QMCLeafB.SlackRoute.leafB_of_slack_verdict (o := fun G t => QMCLeafB.SlackRoute.sbit (eng G) t)
    eng (fun _ _ => rfl) ho QMCLeafB.BrickRQ.Rq_poly

/-! ## 3.  The verdict form: a sound bit needs no engine and no agreement

`Check_BitProgram_m3.lean` removed the engine slot of the *exact* route by observing that a
decider satisfying the two constructors of `Answer` *is* an engine, with the answer bit equal to
the decider by construction.  The same observation at the leaf's slacks removes the engine slot of
the slack route, and with it the agreement hypothesis.  What remains is a single specification:
`Soundε`. -/

/-- **A sound slack verdict.**  `b G t = true` carries an actual unit-diagonal semidefinite point
whose trace is at most `t + Rq G/40000`; `b G t = false` carries a refutation: every feasible
point has trace at least `t − Rq G/40000`.  These are exactly the two constructors of
`Answerε (wMatrix G) t (Rq/40000) (Rq/40000)`, so `Soundε b` says precisely that "the engine slot
is filled by `b`", with no appeal to excluded middle in the specification itself. -/
def Soundε (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) : Prop :=
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), b G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ) + ((Rq G / 40000 : ℚ) : ℝ)) ∧
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), b G t = false →
      ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD Z →
          (t : ℝ) - ((Rq G / 40000 : ℚ) : ℝ) ≤ (QMCLeafB.wMatrix G * Z).trace)

/-- A Boolean that is not `true` is `false`. -/
theorem bool_eq_false_of_ne_true {v : Bool} (h : ¬ (v = true)) : v = false := by
  cases v with
  | true => exact absurd rfl h
  | false => rfl

/-- **The engine a sound slack verdict induces.**  On `true` the witness is extracted from
soundness by `Classical.choice` — this is the *mathematical* direction, never part of the
computation; on `false` the refutation is the soundness proof itself. -/
noncomputable def engineOfε (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) (hb : Soundε b)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.AnswerProducer.Answerε (QMCLeafB.wMatrix G) t (Rq G / 40000) (Rq G / 40000) :=
  if h : b G t = true then
    QMCLeafB.AnswerProducer.Answerε.witness (hb.1 G t h).choose (hb.1 G t h).choose_spec.1
      (hb.1 G t h).choose_spec.2
  else
    QMCLeafB.AnswerProducer.Answerε.refuted (hb.2 G t (bool_eq_false_of_ne_true h))

/-- **The induced engine's verdict bit is the verdict.**  So a sound verdict needs no separate
`hag : sbit (eng G) t = o G t` proof: `Answerε`'s two constructors force the engine to be built
exactly this way. -/
theorem sbit_engineOfε (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) (hb : Soundε b)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.SlackRoute.sbit (engineOfε b hb G) t = b G t := by
  cases h : b G t with
  | true =>
      have he : engineOfε b hb G t
          = QMCLeafB.AnswerProducer.Answerε.witness (hb.1 G t h).choose
              (hb.1 G t h).choose_spec.1 (hb.1 G t h).choose_spec.2 := by
        unfold engineOfε
        rw [dif_pos h]
      simp only [QMCLeafB.SlackRoute.sbit, he]
  | false =>
      have hne : ¬ (b G t = true) := by rw [h]; simp
      have he : engineOfε b hb G t
          = QMCLeafB.AnswerProducer.Answerε.refuted (hb.2 G t (bool_eq_false_of_ne_true hne)) := by
        unfold engineOfε
        rw [dif_neg hne]
      simp only [QMCLeafB.SlackRoute.sbit, he]

/-- **The residual of the whole campaign on the slack route.**  One sound verdict bit and one
`Poly` program for it give `d9f601e5`.  Everything else — the thirteen-call bisection, the value
form, the sandwich, the `W/10000` budget, the `TM2` package, the total-weight program — is
already discharged. -/
theorem solution_of_ho
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hsound : Soundε o)
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)) :
    SolutionStatement :=
  solution_of_eng (engineOfε o hsound) (by
    have h : (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        QMCLeafB.SlackRoute.sbit (engineOfε o hsound p.1.1) p.2)
        = fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2 :=
      funext fun p => sbit_engineOfε o hsound p.1.1 p.2
    rw [h]
    exact ho)

/-! ## 4.  The drop-in hook for the loop bricks

The simulation bricks deliver a `Poly` program for a *function* `sim` of the encoded request, and
a proof that its output is the verdict.  Rewriting under `Poly` is `PolyProgram.congr`, so the
program can be handed in as `sim` and the `Poly` goal for `o` never has to be restated. -/

/-- **A `Poly` statement is invariant under pointwise equality.** -/
theorem poly_of_pointwise {α β : Type} [Coding α] [Coding β] {f g : α → β}
    (hf : Automatic.Poly f) (h : ∀ a, f a = g a) : Automatic.Poly g :=
  ⟨hf.program.congr g h⟩

/-- **The simulation drops in.**  `sim` is *any* function of the encoded request and the rational
threshold (the unrolled simulate of `brick-loop-poly`), `hspec` says its output is the sound
verdict `o`, and `hprog` is its program.  Nothing about the internal shape of `sim` is assumed
here: the loop bricks are free to build it out of their own iterate state. -/
theorem solution_of_program
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hsound : Soundε o)
    (sim : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → Bool)
    (hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), sim p = o p.1.1 p.2)
    (hprog : Automatic.Poly sim) :
    SolutionStatement :=
  solution_of_ho o hsound (poly_of_pointwise hprog hspec)

/-! ## 5.  The two slacks are inside the leaf's precision budget

`leafB_of_slack_verdict` charges `Rq/32768 + (εw + εr)/4` against the value; at
`εw = εr = Rq/40000` the second term is `Rq/160000 = W/80000`, and `Rq = 2W` gives
`W/16384 + W/80000 ≤ W/10000`.  The theorem does this arithmetic internally; it is recorded here
so that the budget claim is a stand-alone, checkable fact. -/

/-- The two slacks, added. -/
theorem slack_sum (G : QuantumMaxCutEnergy.Input) :
    Rq G / 40000 + Rq G / 40000 = Rq G / 20000 := by
  ring

/-- The graph total weight `Rq G = 2 ∑ₑ wₑ`. -/
theorem Rq_eq_two_sum (G : QuantumMaxCutEnergy.Input) :
    Rq G = 2 * ∑ e, ((G.weights e : ℚ≥0) : ℚ) := rfl

/-- **The precision budget, in the leaf's own units**: the two slacks may take
`Rq G / 20000 = W/10000` between them, while phase 4's slack driver allows up to `W/7500`. -/
theorem slack_budget (G : QuantumMaxCutEnergy.Input) :
    ((Rq G / 40000 : ℚ) : ℝ) + ((Rq G / 40000 : ℚ) : ℝ)
      = (∑ e, (G.weights e : ℝ)) / 10000 ∧
    (∑ e, (G.weights e : ℝ)) / 10000 ≤ (∑ e, (G.weights e : ℝ)) / 7500 := by
  have hR : ((Rq G : ℚ) : ℝ) = 2 * ∑ e, (G.weights e : ℝ) := by
    rw [Rq_eq_two_sum]; push_cast; ring
  have hW0 : (0 : ℝ) ≤ ∑ e, (G.weights e : ℝ) :=
    Finset.sum_nonneg fun e _ => by
      have := (G.weights e).2
      exact_mod_cast this
  constructor
  · push_cast
    rw [hR]
    ring
  · refine div_le_div_of_nonneg_left hW0 (by norm_num) (by norm_num)


/-! ## 6.  The bracket clamp: a verdict that is only sound inside the driver's bracket

The phase-4 engine contract the campaign actually has is *bracket-restricted*
(`QMCLeafB.ThresholdDriver.answer_of_range`, `RangeAnswerFamily` in
`Check_LeafB_Phase4_Integration`): an ellipsoid loop can certify the body only for thresholds
`−Rq G ≤ t ≤ 0`, which is all the driver ever asks.  But `Answerε`'s contract — and therefore
`Soundε` — is total in `t`, so a bracket-restricted verdict bit cannot be fed to the closing
theorem unchanged.

The extension is free, and this section does it once and for all.  Outside the bracket the answer
is forced by two classical facts:

* `t ≥ 0`: the identity is feasible with trace `0`, so `true` is a sound witness;
* `t < −Rq G`: every unit-diagonal semidefinite `Z` has `tr(wMatrix G · Z) ≥ −∑ᵢⱼ|Aᵢⱼ| = −Rq G`,
  so `false` is a sound refutation.

`clampBit` is that extension, `soundε_clampBit` transfers soundness, and `poly_clampBit` shows the
extension costs nothing computationally: two rational comparisons and an `ite`.  So the loop bricks
may prove soundness on the bracket only, which is what an ellipsoid run can deliver. -/

/-- **Soundness of a verdict bit inside the driver's bracket.**  `Soundε` with the two clauses
restricted to `−Rq G ≤ t ≤ 0`; this is the contract an ellipsoid simulation can actually meet. -/
def SoundεOnBracket (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) : Prop :=
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), -Rq G ≤ t → t ≤ 0 → b G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ) + ((Rq G / 40000 : ℚ) : ℝ)) ∧
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), -Rq G ≤ t → t ≤ 0 → b G t = false →
      ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD Z →
          (t : ℝ) - ((Rq G / 40000 : ℚ) : ℝ) ≤ (QMCLeafB.wMatrix G * Z).trace)

/-- A total `Soundε` verdict is sound on the bracket. -/
theorem soundεOnBracket_of_soundε {b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool}
    (hb : Soundε b) : SoundεOnBracket b :=
  ⟨fun G t _ _ h => hb.1 G t h, fun G t _ _ h => hb.2 G t h⟩

/-- **The bracket clamp.**  Below the bracket the verdict is `false` (nothing feasible reaches
there), above it `true` (the identity does), and inside it the engine's own bit. -/
noncomputable def clampBit (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Bool :=
  if decide (t < -Rq G) then false else if decide ((0 : ℚ) ≤ t) then true else b G t

/-- **Below the start of the bracket the refutation is free**: `−Rq` is a hard floor for the trace
on the feasible set. -/
theorem neg_Rq_le_trace (G : QuantumMaxCutEnergy.Input) (Z : Matrix (Fin G.n) (Fin G.n) ℝ)
    (hZ : ModernConvex.Relaxations.IsUnitDiagPSD Z) :
    -((Rq G : ℚ) : ℝ) ≤ (QMCLeafB.wMatrix G * Z).trace := by
  have h := QMCLeafB.AnswerProducer.neg_abs_sum_le_trace (QMCLeafB.wMatrix G) Z hZ
  rw [Rq_abs_sum] at h
  exact h

/-- **Above the bracket the witness is free**: the identity has trace `0`. -/
theorem one_trace_eq_zero (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.wMatrix G * 1).trace = 0 := by
  rw [QMCLeafB.AnswerProducer.trace_mul_one]
  exact Finset.sum_eq_zero fun i _ => QMCLeafB.wMatrix_apply_of_eq

/-- **The clamp preserves soundness.**  So a verdict proved correct on the driver's bracket is a
sound *total* verdict after two comparisons. -/
theorem soundε_clampBit (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool)
    (hb : SoundεOnBracket b) : Soundε (clampBit b) := by
  have hεw : ∀ G : QuantumMaxCutEnergy.Input, (0 : ℝ) ≤ ((Rq G / 40000 : ℚ) : ℝ) := by
    intro G
    have h := Rq_nonneg G
    have : (0 : ℚ) ≤ Rq G / 40000 := by linarith
    exact_mod_cast this
  constructor
  · -- the `true` side
    intro G t ht
    by_cases h1 : t < -Rq G
    · rw [clampBit, if_pos (by simpa using h1)] at ht
      exact absurd ht (by simp)
    · by_cases h2 : (0 : ℚ) ≤ t
      · rw [clampBit, if_neg (by simpa using h1), if_pos (by simpa using h2)] at ht
        refine ⟨1, QMCLeafB.AnswerProducer.isUnitDiagPSD_one, ?_⟩
        rw [one_trace_eq_zero]
        have ht0 : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h2
        linarith [hεw G]
      · rw [clampBit, if_neg (by simpa using h1), if_neg (by simpa using h2)] at ht
        exact hb.1 G t (not_lt.mp h1) (le_of_lt (not_le.mp h2)) ht
  · -- the `false` side
    intro G t ht
    by_cases h1 : t < -Rq G
    · rw [clampBit, if_pos (by simpa using h1)] at ht
      intro Z hZ
      have hfloor := neg_Rq_le_trace G Z hZ
      have htR : (t : ℝ) < -((Rq G : ℚ) : ℝ) := by exact_mod_cast h1
      linarith [hεw G]
    · by_cases h2 : (0 : ℚ) ≤ t
      · rw [clampBit, if_neg (by simpa using h1), if_pos (by simpa using h2)] at ht
        exact absurd ht (by simp)
      · rw [clampBit, if_neg (by simpa using h1), if_neg (by simpa using h2)] at ht
        exact hb.2 G t (not_lt.mp h1) (le_of_lt (not_le.mp h2)) ht

/-- **The clamp is a program.**  Two rational comparisons (`t < −Rq G`, `0 ≤ t`) around the
engine's own bit; `Rq` is `QMCLeafB.BrickRQ.Rq_poly`. -/
theorem poly_clampBit (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool)
    (hb : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => b p.1.1 p.2)) :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => clampBit b p.1.1 p.2) := by
  have hfst : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        (p.1 : QuantumMaxCutEnergy.Input × List Bool)) := Automatic.Poly.fst
  have hsnd : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (p.2 : ℚ)) := Automatic.Poly.snd
  have hRq : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => Rq p.1.1) :=
    Automatic.Poly.comp
      (f := fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1) QMCLeafB.BrickRQ.Rq_poly hfst
  have hneg : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => -Rq p.1.1) :=
    Automatic.Poly.comp (f := fun q : ℚ => -q) (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => Rq p.1.1)
      Automatic.Poly.rat_neg hRq
  have hlt : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      decide (p.2 < -Rq p.1.1)) :=
    Automatic.Poly.comp
      (f := fun q : ℚ × ℚ => decide (q.1 < q.2))
      (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (p.2, -Rq p.1.1))
      Automatic.Poly.rat_lt (Automatic.Poly.pair hsnd hneg)
  have hle : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      decide ((0 : ℚ) ≤ p.2)) :=
    Automatic.Poly.comp
      (f := fun q : ℚ × ℚ => decide (q.1 ≤ q.2))
      (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => ((0 : ℚ), p.2))
      Automatic.Poly.rat_le (Automatic.Poly.pair (Automatic.Poly.const 0) hsnd)
  have hinner : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      if decide ((0 : ℚ) ≤ p.2) then true else b p.1.1 p.2) :=
    Automatic.Poly.ite hle (Automatic.Poly.const true) hb
  have houter : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      if decide (p.2 < -Rq p.1.1) then false
        else if decide ((0 : ℚ) ≤ p.2) then true else b p.1.1 p.2) :=
    Automatic.Poly.ite hlt (Automatic.Poly.const false) hinner
  exact houter

/-- **The bracket-restricted stroke.**  This is the form the loop bricks should target: prove the
verdict only on `−Rq G ≤ t ≤ 0`, prove it is a program, and the leaf is closed. -/
theorem solution_of_bracket_verdict
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hsound : SoundεOnBracket o)
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)) :
    SolutionStatement :=
  solution_of_ho (clampBit o) (soundε_clampBit o hsound) (poly_clampBit o ho)

/-- The bracket form with the program handed in as an arbitrary function, as `solution_of_program`. -/
theorem solution_of_bracket_program
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hsound : SoundεOnBracket o)
    (sim : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → Bool)
    (hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), sim p = o p.1.1 p.2)
    (hprog : Automatic.Poly sim) :
    SolutionStatement :=
  solution_of_bracket_verdict o hsound (poly_of_pointwise hprog hspec)


/-! ## 7.  The residual is computability, not existence

The specification `Soundε` is a statement about a Boolean; it would be worthless if it were
unsatisfiable, or if it smuggled in mathematical content.  It does neither: the *truth* about the
threshold body — decide, classically, whether a feasible point with
`tr(wMatrix G · X) ≤ t + εw` exists — is sound.  So `Soundε` is inhabited, and what the campaign
still owes is exactly the computability of a sound verdict, nothing else.  This is the slack
analogue of `Check_BitProgram_m3`'s `sound_feasBit`. -/

/-- The classical truth bit at the leaf's slack: `true` when a unit-diagonal semidefinite point
overshoots the threshold by at most `Rq G/40000`. -/
noncomputable def truthBit (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Bool := by
  classical
  exact if h : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ) + ((Rq G / 40000 : ℚ) : ℝ)
    then true else false

/-- **The truth is a sound slack verdict.** -/
theorem soundε_truthBit : Soundε truthBit := by
  classical
  have hε : ∀ G : QuantumMaxCutEnergy.Input, (0 : ℝ) ≤ ((Rq G / 40000 : ℚ) : ℝ) := by
    intro G
    have h := Rq_nonneg G
    have h' : (0 : ℚ) ≤ Rq G / 40000 := by linarith
    exact_mod_cast h'
  constructor
  · intro G t ht
    by_cases h : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ) + ((Rq G / 40000 : ℚ) : ℝ)
    · rwa [truthBit, dif_pos h] at ht
    · rw [truthBit, dif_neg h] at ht
      exact absurd ht (by simp)
  · intro G t ht Z hZ
    by_cases h : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ) + ((Rq G / 40000 : ℚ) : ℝ)
    · rw [truthBit, dif_pos h] at ht
      exact absurd ht (by simp)
    · have hnot : ¬ ((QMCLeafB.wMatrix G * Z).trace
          ≤ (t : ℝ) + ((Rq G / 40000 : ℚ) : ℝ)) := fun hc => h ⟨Z, hZ, hc⟩
      have hlt := not_le.mp hnot
      linarith [hε G]

/-- **`Soundε` is inhabited**: the residual of the leaf is a computability statement. -/
theorem exists_soundε :
    ∃ o : QuantumMaxCutEnergy.Input → ℚ → Bool, Soundε o :=
  ⟨truthBit, soundε_truthBit⟩

/-- The same on the driver's bracket. -/
theorem exists_soundε_bracket :
    ∃ o : QuantumMaxCutEnergy.Input → ℚ → Bool, SoundεOnBracket o :=
  ⟨truthBit, soundεOnBracket_of_soundε soundε_truthBit⟩

/-- **The residual, as one existential**: the leaf follows from the existence of a *computable*
sound verdict. -/
theorem solution_of_exists_sound
    (h : ∃ o : QuantumMaxCutEnergy.Input → ℚ → Bool, Soundε o ∧
      Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)) :
    SolutionStatement := by
  obtain ⟨o, hs, hp⟩ := h
  exact solution_of_ho o hs hp

/-- The same, bracket form. -/
theorem solution_of_exists_sound_bracket
    (h : ∃ o : QuantumMaxCutEnergy.Input → ℚ → Bool, SoundεOnBracket o ∧
      Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)) :
    SolutionStatement := by
  obtain ⟨o, hs, hp⟩ := h
  exact solution_of_bracket_verdict o hs hp

end QMCLeafB.FinishLine

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.FinishLine.solutionStatement_iff_wMatrix
#print axioms QMCLeafB.FinishLine.solution_of_eng
#print axioms QMCLeafB.FinishLine.Soundε
#print axioms QMCLeafB.FinishLine.engineOfε
#print axioms QMCLeafB.FinishLine.sbit_engineOfε
#print axioms QMCLeafB.FinishLine.solution_of_ho
#print axioms QMCLeafB.FinishLine.poly_of_pointwise
#print axioms QMCLeafB.FinishLine.solution_of_program
#print axioms QMCLeafB.FinishLine.slack_budget
#print axioms QMCLeafB.FinishLine.soundεOnBracket_of_soundε
#print axioms QMCLeafB.FinishLine.neg_Rq_le_trace
#print axioms QMCLeafB.FinishLine.one_trace_eq_zero
#print axioms QMCLeafB.FinishLine.soundε_clampBit
#print axioms QMCLeafB.FinishLine.poly_clampBit
#print axioms QMCLeafB.FinishLine.solution_of_bracket_verdict
#print axioms QMCLeafB.FinishLine.solution_of_bracket_program
#print axioms QMCLeafB.FinishLine.soundε_truthBit
#print axioms QMCLeafB.FinishLine.exists_soundε
#print axioms QMCLeafB.FinishLine.exists_soundε_bracket
#print axioms QMCLeafB.FinishLine.solution_of_exists_sound
#print axioms QMCLeafB.FinishLine.solution_of_exists_sound_bracket

namespace QMCLeafB.FinishLine
open QuantumMaxCutEnergy
local instance instRequestCodingChk : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩
#check @QMCLeafB.FinishLine.solution_of_ho
#check @QMCLeafB.FinishLine.solution_of_eng
#check @QMCLeafB.FinishLine.solution_of_program
#check @QMCLeafB.FinishLine.solution_of_bracket_verdict
#check @QMCLeafB.FinishLine.solution_of_bracket_program
#check @QMCLeafB.FinishLine.exists_soundε
#check @QMCLeafB.FinishLine.solution_of_exists_sound
end QMCLeafB.FinishLine


