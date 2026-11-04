-- Prove2me | Definitions.Def_QMCLeafB_targetAudit
-- name    : QMCLeafB_targetAudit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:29:16.630836+00:00
-- url     : https://prove2.me/theorems/205e448e-4fbf-45fe-8269-c5b3fa9c4d8e
-- title:
--   QMCLeafB targetAudit
-- statement:
--   # leaf B phase 18 — brick `target-audit` (swarm `smw1i2drp`, member m7, direction d7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_Core
import Definitions.Def_QMCLeafB_brick_finish_line
import Definitions.Def_QMCLeafB_zeroedge_m6
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 18 — brick `target-audit` (swarm `smw1i2drp`, member m7, direction d7)

**This file audits the target, not the chain.**  The endgame's business is to produce
`QMCLeafB.FinishLine.SolutionStatement`.  Before anyone spends another phase closing its residuals it
is worth asking whether that sentence

  (i) is the sentence the platform asked for (`d9f601e5`),
  (ii) has any slack that would let a residual be dodged (a junk `S`, a junk `L`, a vacuous branch),
  (iii) is true at the degenerate end of the input space, so that the leaf is not refuted outright.

The answers here are all negative except (iii) — which is the honest, useful outcome:

* §1 `Sentence` — the `d9f601e5` sentence transcribed afresh in this file (not copied from
  `Def_QMCLeafB_brick_finish_line`), and `sentence_eq_target : Sentence ↔ SolutionStatement`.  The
  transcription is checked by the kernel, so the target is not a paraphrase.
* §2 `solutionStatement_iff_pinned` — **the `∃ S` slot is not slack.**  `IsMaxcutSDPValue A S` is an
  `IsLUB`, hence `S` is unique (`QMCLeafBExistence.isMaxcutSDPValue_unique`), so the target is
  equivalent to the (strictly stronger-looking, in fact equal) pinned form in which the machine's
  output must be within `W/10000` of **the** max-cut SDP value of every input:
  `∀ G, ∀ S, IsMaxcutSDPValue (wMatrix G) S → …`.  So there is no residual that can be dodged by
  choosing a convenient `S`.
* §3 `output_lower_bound` — **the target is not satisfiable by a junk output.**  From the shelf's
  sandwich `W/2 ≤ S ≤ W` (`QMCLeafBExistence.forall_input_value_sandwich`) the conclusion
  `S - L ≤ W/10000` forces `L G ≥ (4999/10000)·W G` at every input.  The machine the leaf asks for
  must therefore *output a constant fraction of the whole edge weight*, not `0`.
* §4 `zero_output_impossible` — the same fact as a refutation: on any input of positive total weight
  the output `L ≡ 0` fails the leaf's own conclusion.  (`example` in §5 exhibits such an input, so §4
  is not vacuous.)
* §6 `zero_edge_end` — and the degenerate end is fine: on zero-weight inputs `L := 0` *does* satisfy
  the conclusion (`QMCLeafB.ZeroEdge.leaf_at_zero_weight`).  So the leaf is not refuted, and its
  content lives exactly on `0 < W G`.
* §7 axiom audit.

What this file deliberately does not do: it does not prove `SolutionStatement`, and it does not
pretend a residual is discharged.  It records, machine-checked, that the sentence the phase-17
residual acceptance was standing in for is the real one, that it is sharp in `S`, and that it is
non-vacuous in `L`.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false

namespace QMCLeafB.TargetAudit

open QuantumMaxCutEnergy

/-! ## 1.  The sentence of `d9f601e5`, transcribed afresh

`Def_QMCLeafB_brick_finish_line` states the sentence as `SolutionStatement`.  The transcription below
is written out again from the platform's statement of
`QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2`
(theorem id `d9f601e5-8c68-4369-a27d-701e73e686b8`) — same quantifiers, same `Matrix.of`, same
`∑ e, w e / 10000`.  `sentence_eq_target` is the kernel's check that the two are the same
proposition; it is `Iff.rfl` and would not typecheck if a single token differed in content. -/

/-- **`d9f601e5`**, written out again (verbatim transcription). -/
def Sentence : Prop :=
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

/-- **The transcription is the target.**  Kernel-checked identity of the two propositions. -/
theorem sentence_eq_target : Sentence ↔ QMCLeafB.FinishLine.SolutionStatement :=
  Iff.rfl

/-- The same identity in the `wMatrix` spelling, which is the form every closing theorem uses
(`QMCLeafB.wMatrix` is *defined* as that `Matrix.of`). -/
theorem sentence_eq_target_wMatrix :
    Sentence ↔
      ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
        Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
          QuantumMaxCutEnergy.encodeValue
          (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
        ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
          ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
          (L G : ℝ) ≤ S ∧
          S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  Iff.rfl

/-! ## 2.  The value slot is pinned: `S` is unique, so `∃ S` is not slack -/

/-- **`S` is unique for the target's own matrix.**  Hence the `∃ S` of `d9f601e5` does not let a
prover pick a convenient value: the sentence is about *the* max-cut SDP value. -/
theorem target_value_unique (G : QuantumMaxCutEnergy.Input) {S S' : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S)
    (hS' : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S') : S = S' :=
  QMCLeafBExistence.isMaxcutSDPValue_unique hS hS'

/-- **The pinned form of the target.**  `d9f601e5` is equivalent to the quantified form in which the
output must sit within `W/10000` below *every* max-cut SDP value of the input — i.e. the residual
cannot be discharged at a hand-picked `S`. -/
theorem solutionStatement_iff_pinned :
    QMCLeafB.FinishLine.SolutionStatement ↔
      ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
        Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
          QuantumMaxCutEnergy.encodeValue
          (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
        ∀ G : QuantumMaxCutEnergy.Input, ∀ S : ℝ,
          ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S →
          (L G : ℝ) ≤ S ∧
          S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  constructor
  · rintro ⟨L, hL, hval⟩
    refine ⟨L, hL, fun G S hS => ?_⟩
    obtain ⟨S₀, hS₀, hle, hgap⟩ := hval G
    have heq : S = S₀ := target_value_unique G hS hS₀
    subst heq
    exact ⟨hle, hgap⟩
  · rintro ⟨L, hL, hval⟩
    refine ⟨L, hL, fun G => ?_⟩
    obtain ⟨S, hS⟩ := QMCLeafBExistence.exists_isMaxcutSDPValue (QMCLeafB.wMatrix G)
    exact ⟨S, hS, hval G S hS⟩

/-! ## 3.  The target is not satisfiable by a junk output

The shelf's sandwich is `W/2 ≤ S ≤ W` at every input.  Together with `S - L ≤ W/10000` it pins the
machine's output from below: the leaf *forces* a constant fraction of the total edge weight. -/

/-- **Every admissible output is at least `(4999/10000)·W`.** -/
theorem output_lower_bound {L : QuantumMaxCutEnergy.Input → ℚ≥0}
    (hL : ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
      (L G : ℝ) ≤ S ∧
      S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) :
    ∀ G : QuantumMaxCutEnergy.Input,
      (4999 / 10000 : ℝ) * (∑ e, (G.weights e : ℝ)) ≤ (L G : ℝ) := by
  intro G
  obtain ⟨S, hS, -, hgap⟩ := hL G
  obtain ⟨S', hS', -, hhalf, -⟩ := QMCLeafBExistence.forall_input_value_sandwich G
  have heq : S = S' := target_value_unique G hS hS'
  rw [heq] at hgap
  have hhalf' : (∑ e, (G.weights e : ℝ)) / 2 ≤ S' := hhalf
  linarith

/-- **The trivial programme is admissible at slack `W/2`, and only there.**  Taking the output to be
`W G/2` satisfies the leaf's numerical conclusion with the error term `W/2` at every input (this is the
shelf sandwich `W/2 ≤ S ≤ W` and nothing else), and `W/2` is poly-computable — that is the phase-17
`leaf_sentence_half_slack_unconditional` shape.  The leaf asks for `W/10000`, i.e. 5000× tighter, which
is why no constant-output shortcut survives §4. -/
theorem half_slack_admissible :
    ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
      (∑ e, (G.weights e : ℝ)) / 2 ≤ S ∧
      S - (∑ e, (G.weights e : ℝ)) / 2 ≤ (∑ e, (G.weights e : ℝ)) / 2 := by
  intro G
  obtain ⟨S, hS, -, hhalf, hle⟩ := QMCLeafBExistence.forall_input_value_sandwich G
  exact ⟨S, hS, hhalf, by linarith⟩

/-! ## 4.  The refutation of the junk output

The most tempting "residual dodging" move is to take the machine's output to be `0` (it is
`ℚ≥0`-valued, and `0` is the cheapest program in the fragment).  On an input of positive total weight
that fails, and §5 shows such an input exists. -/

/-- **`L ≡ 0` is not admissible on a positive-weight input.** -/
theorem zero_output_impossible (G : QuantumMaxCutEnergy.Input)
    (hW : 0 < ∑ e, (G.weights e : ℝ)) :
    ¬ ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
      (0 : ℝ) ≤ S ∧
      S - (0 : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  rintro ⟨S, hS, -, hgap⟩
  obtain ⟨S', hS', -, hhalf, -⟩ := QMCLeafBExistence.forall_input_value_sandwich G
  have heq : S = S' := target_value_unique G hS hS'
  rw [heq] at hgap
  linarith

/-! ## 5.  The refutation bites: an input of positive total weight -/

/-- The two-vertex graph with a single edge of weight `1`. -/
def edgeG : QuantumMaxCutEnergy.Input where
  n := 2
  weights := fun _ => 1

/-- The single edge of the two-vertex graph. -/
def edgeOf2 : QuantumMaxCutEnergy.Edge 2 := ⟨(0, 1), by decide⟩

/-- **The two-vertex graph has positive total weight.**  No card computation: one summand is `1` and
every summand is nonnegative. -/
theorem edgeG_weight : (0 : ℝ) < ∑ e, (edgeG.weights e : ℝ) := by
  have hmem : edgeOf2 ∈ (Finset.univ : Finset (QuantumMaxCutEnergy.Edge 2)) := Finset.mem_univ _
  have hle : ((edgeG.weights edgeOf2 : ℚ≥0) : ℝ)
      ≤ ∑ e, (edgeG.weights e : ℝ) :=
    Finset.single_le_sum (f := fun e => ((edgeG.weights e : ℚ≥0) : ℝ))
      (fun i _ => by positivity) hmem
  have h1 : ((edgeG.weights edgeOf2 : ℚ≥0) : ℝ) = 1 := by
    show ((1 : ℚ≥0) : ℝ) = 1
    norm_num
  rw [h1] at hle
  linarith

/-- **There is an input with positive total weight**, so §4 refutes `L ≡ 0` at a real input. -/
theorem exists_pos_weight : ∃ G : QuantumMaxCutEnergy.Input, 0 < ∑ e, (G.weights e : ℝ) :=
  ⟨edgeG, edgeG_weight⟩

/-- **The junk output is genuinely refuted.** -/
theorem zero_output_refuted :
    ¬ (∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (0 : ℝ) ≤ S ∧
        S - (0 : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) := by
  intro h
  obtain ⟨G, hW⟩ := exists_pos_weight
  exact zero_output_impossible G hW (h G)

/-! ## 6.  The degenerate end is satisfied, so the leaf is not refuted there

Zero-weight inputs are the only place a constant output survives, and there the leaf's conclusion is
already a theorem of the shelf.  So the target's content is exactly `0 < W G`, and no residual may be
restricted to the degenerate inputs. -/

/-- **`L := 0` satisfies the conclusion on zero-weight inputs.** -/
theorem zero_edge_end (G : QuantumMaxCutEnergy.Input)
    (hw : ∀ e : QuantumMaxCutEnergy.Edge G.n, G.weights e = 0) :
    ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
      (0 : ℝ) ≤ S ∧
      S - (0 : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.ZeroEdge.leaf_at_zero_weight G hw

/-! ## 7.  Summary of the audit, as a single kernel-checked statement

Read together: the target is the platform's sentence (§1), it is sharp in `S` (§2), it forces
`L G ≥ (4999/10000)·W G` at every input (§3) so it cannot be discharged by a junk output (§4, §5), and
it is true at the degenerate inputs (§6) so neither is it refuted.  The residual list of the phase-18
problem is therefore load-bearing in the strong sense: no branch of the sentence is slack. -/

/-- **The audit in one line.**  A candidate `L` satisfies the leaf's conclusion for *some* value slot
iff it does so for the value the graph actually has, and then it is at least `4999/10000` of the
input's total weight. -/
theorem target_audit (L : QuantumMaxCutEnergy.Input → ℚ≥0) :
    ((∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) ↔
      (∀ G : QuantumMaxCutEnergy.Input, ∀ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S →
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000)) ∧
    ((∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) →
      ∀ G : QuantumMaxCutEnergy.Input,
        (4999 / 10000 : ℝ) * (∑ e, (G.weights e : ℝ)) ≤ (L G : ℝ)) := by
  refine ⟨⟨fun h G S hS => ?_, fun h G => ?_⟩, output_lower_bound⟩
  · obtain ⟨S₀, hS₀, hle, hgap⟩ := h G
    have heq : S = S₀ := target_value_unique G hS hS₀
    subst heq
    exact ⟨hle, hgap⟩
  · obtain ⟨S, hS⟩ := QMCLeafBExistence.exists_isMaxcutSDPValue (QMCLeafB.wMatrix G)
    exact ⟨S, hS, h G S hS⟩

/-! ## 8.  What the leaf's residual *is*: a two-sided threshold decision on the SDP value

`FinchLine`'s route reduces the whole sentence to one existential,
`QMCLeafB.FinishLine.solution_of_exists_sound_bracket`:

    (∃ o, SoundεOnBracket o ∧ Automatic.Poly (fun p => o p.1.1 p.2)) → SolutionStatement

so everything the run-records/trace-budget residuals are for has to end in `SoundεOnBracket o`.  This
section pins down what that predicate actually asks.  Write `V G = ∑ᵢ ∑ⱼ (wMatrix G)ᵢⱼ`; the shelf's
`maxcut_objective_eq` gives `tr(wMatrix G · X) = V G − 4·objective X`, and `V G = Rq G` (§8.1), so the
two branches of `SoundεOnBracket`, which are statements about `tr`, become statements about the SDP
**value**:

* `o G t = true` is sound at `t` **iff** the value is at least `(Rq G − t − Rq G/40000)/4`,
* `o G t = false` is sound at `t` **iff** the value is at most `(Rq G − t + Rq G/40000)/4`.

There is no slack between the two: `soundεOnBracket_iff_threshold` says a sound bracket bit is
*exactly* a decision that tracks the max-cut SDP value to within `Rq G/40000` of the trace scale.  So
the leaf's residual is one number per input — the value — computed to relative precision `1/20000`,
and no branch of it can be dodged.  This is the audit conclusion of §1–§7 in machine-checked form.
-/

/-- **`∑ᵢ ∑ⱼ (wMatrix G)ᵢⱼ = Rq G`**: the trace ledger's `Rq` is the matrix's total mass, so the
objective/trace dictionary below carries no extra constant. -/
theorem wMatrix_sum_eq_Rq (G : QuantumMaxCutEnergy.Input) :
    (∑ i, ∑ j, QMCLeafB.wMatrix G i j) = ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
  have h := QMCLeafB.EngineRuntime.Rq_abs_sum G
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (abs_of_nonneg (QMCLeafB.wMatrix_nonneg G i j)).symm

/-- The lower threshold attached to a bracket point: a `true` at `t` is sound exactly above it. -/
noncomputable def threshold (G : QuantumMaxCutEnergy.Input) (t : ℚ) : ℝ :=
  (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) - (t : ℝ)
    - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) / 4

/-- The upper threshold: a `false` at `t` is sound exactly below it. -/
noncomputable def cothreshold (G : QuantumMaxCutEnergy.Input) (t : ℚ) : ℝ :=
  (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) - (t : ℝ)
    + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) / 4

/-- **The dictionary.**  For a feasible `X`, the leaf's trace bound at `t` is the objective bound at
`threshold G t`. -/
theorem trace_le_iff_objective (G : QuantumMaxCutEnergy.Input)
    (X : Matrix (Fin G.n) (Fin G.n) ℝ) (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) (t : ℚ) :
    ((QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ)
        + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
      ↔ threshold G t ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (QMCLeafB.wMatrix G) X := by
  have hsym : Xᵀ = X := QMCLeafB.transpose_eq_of_posSemidef hX.1
  have hobj := QMCLeafB.maxcut_objective_eq (QMCLeafB.wMatrix G) X hsym
  rw [hobj, wMatrix_sum_eq_Rq, threshold]
  constructor <;> intro h <;> linarith

/-- The same dictionary in the other direction. -/
theorem objective_le_iff_trace (G : QuantumMaxCutEnergy.Input)
    (X : Matrix (Fin G.n) (Fin G.n) ℝ) (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) (t : ℚ) :
    (ModernConvex.Relaxations.maxcutRelaxationObjective (QMCLeafB.wMatrix G) X ≤ cothreshold G t)
      ↔ ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
          ≤ (QMCLeafB.wMatrix G * X).trace) := by
  have hsym : Xᵀ = X := QMCLeafB.transpose_eq_of_posSemidef hX.1
  have hobj := QMCLeafB.maxcut_objective_eq (QMCLeafB.wMatrix G) X hsym
  rw [hobj, wMatrix_sum_eq_Rq, cothreshold]
  constructor <;> intro h <;> linarith

/-- **`SoundεOnBracket` is a two-sided threshold decision on the value.**  A bracket bit is sound
exactly when, at every bracket point, a `true` certifies that the value is above `threshold G t` and a
`false` certifies that it is below `cothreshold G t`.  Nothing else is asked: the witnesses
(`X`, `Z`) are produced classically by attainment, so the only content of the residual is *deciding*
on which side of the value a threshold lies. -/
theorem soundεOnBracket_iff_threshold {b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool} :
    QMCLeafB.FinishLine.SoundεOnBracket b ↔
      ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
        -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
        ((b G t = true → ∀ S : ℝ,
            ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S → threshold G t ≤ S) ∧
          (b G t = false → ∀ S : ℝ,
            ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S → S ≤ cothreshold G t)) := by
  constructor
  · intro hb G t hlo hhi
    refine ⟨fun ht S hS => ?_, fun hf S hS => ?_⟩
    · obtain ⟨X, hX, htr⟩ := hb.1 G t hlo hhi ht
      have h1 : threshold G t
          ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (QMCLeafB.wMatrix G) X :=
        (trace_le_iff_objective G X hX t).1 htr
      exact le_trans h1 (hS.1 ⟨X, hX, rfl⟩)
    · obtain ⟨X, hX, hSopt⟩ := QMCLeafBExistence.exists_optimal (QMCLeafB.wMatrix G)
      have h1 : (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
          ≤ (QMCLeafB.wMatrix G * X).trace := hb.2 G t hlo hhi hf X hX
      have h2 : ModernConvex.Relaxations.maxcutRelaxationObjective (QMCLeafB.wMatrix G) X
          ≤ cothreshold G t := (objective_le_iff_trace G X hX t).2 h1
      rw [target_value_unique G hS hSopt]
      exact h2
  · intro h
    refine ⟨fun G t hlo hhi ht => ?_, fun G t hlo hhi hf Z hZ => ?_⟩
    · obtain ⟨X, hX, hS⟩ := QMCLeafBExistence.exists_optimal (QMCLeafB.wMatrix G)
      have h1 : threshold G t
          ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (QMCLeafB.wMatrix G) X :=
        (h G t hlo hhi).1 ht _ hS
      exact ⟨X, hX, (trace_le_iff_objective G X hX t).2 h1⟩
    · obtain ⟨X, hX, hS⟩ := QMCLeafBExistence.exists_optimal (QMCLeafB.wMatrix G)
      have h1 : ModernConvex.Relaxations.maxcutRelaxationObjective (QMCLeafB.wMatrix G) X
          ≤ cothreshold G t := (h G t hlo hhi).2 hf _ hS
      have h2 : ModernConvex.Relaxations.maxcutRelaxationObjective (QMCLeafB.wMatrix G) Z
          ≤ cothreshold G t :=
        le_trans (hS.1 ⟨Z, hZ, rfl⟩) h1
      exact (objective_le_iff_trace G Z hZ t).1 h2

local instance instCodingRequestAudit :
    OAI.MetricKMedian.Binary.Automatic.Coding
      (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **The residual, stated without the run machinery.**  Combining §8 with the shelf's
`solution_of_exists_sound_bracket`: the whole leaf is the existence of a `Poly` program that decides,
at each bracket point, on which side of the max-cut SDP value the threshold `t` lies, to relative
precision `1/20000`.  This is the object the per-round records and the trace budget exist to build. -/
theorem leaf_is_threshold_decision
    (ho : ∃ o : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool,
      QMCLeafB.FinishLine.SoundεOnBracket o ∧
        OAI.MetricKMedian.Binary.Automatic.Poly
          (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_exists_sound_bracket ho

/-! ## 9.  Which stroke can consume `DriftExact.runParts_at_interior_exact`

Not part of the sentence, but part of the audit: the residual producer `runParts_at_interior_exact`
(`Solutions/Check_drift_m3.lean`) concludes `RunParts o G t (UnionShallow.paramsKbc2 G)`, and the
round-count function of the RoundGU stroke is definitionally that of `paramsKbc2`.  The GuardT stroke
asks for `LoopClose.paramsShallow`, whose `K` is `Kbc4 …`, so it is a *different finite program* and
cannot consume the producer without a transport.  Recorded here so the assembly cannot be wired to
the wrong stroke. -/
theorem roundGU_roundcount_matches (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
        * QMCLeafB.HalvePerG.mHalve (G.n * G.n)
      = (QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m :=
  rfl

/-! ## 10.  The interior bracket is inhabited, and `hRq` is a real hypothesis

`SolutionStatement`'s consumers (`RoundGUEndgame.solution_roundGU`, `GuardT.endgame_guardT`) quantify
their run obligation only over the *interior* of the bracket
`-Rq G ≤ t` with `t < -Rq G/40000`.  The shelf records the degenerate half of that story
(`QMCLeafB.ZeroEdge.bracket_empty_of_Rq_nonpos`: nothing lives there when `Rq G ≤ 0`).  Here is the
other half: when `Rq G > 0` the interior is **non-empty**, so the run obligation is not discharged by
an empty quantifier — `hd` must actually be inhabited at a point.  Note `Rq G = 2·W` and the shelf's
`runParts_at_interior_exact` carries `hRq : 0 < Rq G`, which is not a consequence of the leaf's own
hypotheses: on an all-zero-weight graph `Rq G = 0`.  So the degenerate end is *not* free and must be
split off (`QMCLeafB.ZeroEdge.leaf_at_zero_weight` is that split). -/

/-- **`t = -Rq G/2` is an interior point of the bracket** whenever `Rq G > 0`. -/
theorem interior_bracket_inhabited (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    ∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq G ≤ t ∧
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  refine ⟨-(QMCLeafB.EngineRuntime.Rq G) / 2, by linarith, ?_⟩
  have hR : (0 : ℝ) < ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by exact_mod_cast hRq
  push_cast
  nlinarith

/-- **`Rq` vanishes on zero-weight inputs**, so `hRq : 0 < Rq G` is an extra hypothesis, not a
theorem.  (The leaf quantifies over these inputs; `ZeroEdge` closes them separately.) -/
theorem Rq_eq_zero_of_zero_weight (G : QuantumMaxCutEnergy.Input)
    (hw : ∀ e : QuantumMaxCutEnergy.Edge G.n, G.weights e = 0) :
    QMCLeafB.EngineRuntime.Rq G = 0 := by
  simp [QMCLeafB.EngineRuntime.Rq, hw]

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.TargetAudit.sentence_eq_target
#print axioms QMCLeafB.TargetAudit.sentence_eq_target_wMatrix
#print axioms QMCLeafB.TargetAudit.target_value_unique
#print axioms QMCLeafB.TargetAudit.solutionStatement_iff_pinned
#print axioms QMCLeafB.TargetAudit.half_slack_admissible
#print axioms QMCLeafB.TargetAudit.output_lower_bound
#print axioms QMCLeafB.TargetAudit.zero_output_impossible
#print axioms QMCLeafB.TargetAudit.edgeG_weight
#print axioms QMCLeafB.TargetAudit.exists_pos_weight
#print axioms QMCLeafB.TargetAudit.zero_output_refuted
#print axioms QMCLeafB.TargetAudit.zero_edge_end
#print axioms QMCLeafB.TargetAudit.target_audit
#print axioms QMCLeafB.TargetAudit.wMatrix_sum_eq_Rq
#print axioms QMCLeafB.TargetAudit.trace_le_iff_objective
#print axioms QMCLeafB.TargetAudit.objective_le_iff_trace
#print axioms QMCLeafB.TargetAudit.soundεOnBracket_iff_threshold
#print axioms QMCLeafB.TargetAudit.leaf_is_threshold_decision
#print axioms QMCLeafB.TargetAudit.roundGU_roundcount_matches
#print axioms QMCLeafB.TargetAudit.interior_bracket_inhabited
#print axioms QMCLeafB.TargetAudit.Rq_eq_zero_of_zero_weight

end QMCLeafB.TargetAudit


