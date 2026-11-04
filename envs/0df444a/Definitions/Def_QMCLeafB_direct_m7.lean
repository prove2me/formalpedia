-- Prove2me | Definitions.Def_QMCLeafB_direct_m7
-- name    : QMCLeafB_direct_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:07:09.188474+00:00
-- url     : https://prove2.me/theorems/108c24b1-770b-46e0-8a88-2b8ef063ffd8
-- title:
--   QMCLeafB direct_m7
-- statement:
--   # leaf B phase 17 — direction `d8` "direct-route": the target sentence's own content (member m7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_finish_line
import Definitions.Def_QMCLeafB_brick_rq_program
import Definitions.Def_QMCLeafB_InterfaceAudit_m2
/-
# leaf B phase 17 — direction `d8` "direct-route": the target sentence's own content (member m7)

Every other direction of this swarm attacks the residual hypothesis `hd` (the RunParts record
bundle) or the glue that consumes it.  This file attacks the *statement* instead: what does
`d9f601e5` assert by itself, and what of it is provable without the TM2 engine at all?

Two answers, both machine-checked here:

* **`leaf_at_half_slack`** — for *every* input `G` the leaf's per-instance conclusion holds with
  `L := (total weight)/2` and slack `(total weight)/2` instead of `(total weight)/10000`, with the
  SDP value pinned by the shelf's exact sandwich `W/2 ≤ S ≤ W`.  So the target sentence is
  inhabited by an explicit, structure-only `L`: nothing about the engine is needed to make the
  sentence *non-vacuous*, and the whole remaining content of the leaf is the factor `5000`
  (= `(1/10000)⁻¹ / (1/2)⁻¹`) of slack.
* **`no_totalWeight_L`** — that factor is not removable by any `L` that sees only the total weight.
  Two inputs with the same total weight have SDP values `1` and `3/4` (single edge vs. flat
  triangle), a gap of `1/4` against a slack of `2·10⁻⁴`.  Hence *every* solution of the leaf must
  evaluate the graph-dependent SDP value to four decimal places: the residual `hd` is not
  replaceable by any weight-sum proxy, and the numeric engine is genuinely needed.

`leaf_sentence_half_slack` states the exact remaining slot of the weakened sentence (a poly-time
program for `W/2`), which is the shelf's own `Rq_poly` business and not re-proved here.

Nothing in this file touches the frozen shelf: it only *reads* `QMCLeafBExistence`'s sandwich and
the `QMCLeafB` dual/primal lemmas that the closing chain already loads.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Direct

open QuantumMaxCutEnergy

/-! ## 0.  Notation: the total edge weight, and the two weight-matrix spellings -/

/-- The leaf's total edge weight `∑ e, w e`, as a real number. -/
def W (G : Input) : ℝ := ∑ e : Edge G.n, (G.weights e : ℝ)

/-- The shelf's `QMCLeafBExistence.weightMatrix` and the closing chain's `QMCLeafB.wMatrix` are the
same matrix (both are the verbatim `Matrix.of` of the target sentence). -/
theorem weightMatrix_eq_wMatrix (G : Input) :
    QMCLeafBExistence.weightMatrix G = QMCLeafB.wMatrix G := rfl

theorem wMatrix_eq_weightMatrix (G : Input) :
    QMCLeafB.wMatrix G = QMCLeafBExistence.weightMatrix G := rfl

/-! ## 1.  The SDP value exists and is sandwiched by the total weight -/

/-- The max-cut SDP value of an input graph exists. -/
theorem exists_sdpValue (G : Input) :
    ∃ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S := by
  obtain ⟨S, hS, -, -⟩ := QMCLeafBExistence.forall_input_value_sandwich G
  exact ⟨S, by rwa [wMatrix_eq_weightMatrix]⟩

/-- **The exact sandwich.**  Any `S` that is the max-cut SDP value of `G`'s weight matrix sits
between half the total weight and the total weight. -/
theorem sdpValue_sandwich (G : Input) {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S) :
    W G / 2 ≤ S ∧ S ≤ W G := by
  obtain ⟨S', hS', -, hlo, hhi⟩ := QMCLeafBExistence.forall_input_value_sandwich G
  have hS'' : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S' := by
    rwa [wMatrix_eq_weightMatrix]
  have hEq : S = S' := hS.unique hS''
  refine ⟨?_, ?_⟩
  · rw [hEq]; exact hlo
  · rw [hEq]; exact hhi

/-! ## 2.  The weakened target, unconditionally, per instance

`L := W/2` is admissible (`W/2 ≤ S`), and its gap is `S − W/2 ≤ W − W/2 = W/2`.  So the leaf's
sentence is satisfiable with the slack `W/2` — 5000 times the campaign's `W/10000`. -/

/-- **The leaf's per-instance conclusion at `L := W/2`, slack `W/2`.** -/
theorem leaf_at_half_slack (G : Input) :
    ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        W G / 2 ≤ S ∧ S - W G / 2 ≤ W G / 2 := by
  obtain ⟨S, hS⟩ := exists_sdpValue G
  obtain ⟨hlo, hhi⟩ := sdpValue_sandwich G hS
  exact ⟨S, hS, hlo, by linarith⟩

/-- **The same at any constant multiple `c ∈ [0, 1/2]`**: `L := c·W` is admissible with gap
`(1 − c)·W`.  `c = 1/2` (`leaf_at_half_slack`) is the best of the family. -/
theorem leaf_at_scaled_slack (G : Input) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) :
    ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        c * W G ≤ S ∧ S - c * W G ≤ (1 - c) * W G := by
  obtain ⟨S, hS⟩ := exists_sdpValue G
  obtain ⟨hlo, hhi⟩ := sdpValue_sandwich G hS
  have hW0 : 0 ≤ W G := by
    rw [W]
    exact Finset.sum_nonneg fun e _ => by positivity
  have hcW : c * W G ≤ W G / 2 := by nlinarith [mul_le_mul_of_nonneg_right hc hW0]
  refine ⟨S, hS, by linarith, by linarith⟩

/-! ## 3.  The statement-level form: only the program for `W/2` is missing

The leaf's sentence with slack `W/2` follows from a poly-time program for the function
`G ↦ ⟨W G / 2, _⟩ : ℚ≥0`.  (`BrickRQ.Rq_poly` already produces a `Poly` program for `Rq = 2W`;
this file does not re-run that wiring, so the slot is stated rather than filled. -/

/-- **The leaf's sentence with the slack relaxed to `W/2`, from a program for `W/2`.** -/
theorem leaf_sentence_half_slack (L : Input → ℚ≥0) (hval : ∀ G, (L G : ℝ) = W G / 2)
    (hprog : Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
      QuantumMaxCutEnergy.encodeValue
      (fun request : Input × List Bool => L request.1))) :
    ∃ L' : Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : Input × List Bool => L' request.1)) ∧
      ∀ G : Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
          (L' G : ℝ) ≤ S ∧ S - (L' G : ℝ) ≤ W G / 2 := by
  refine ⟨L, hprog, fun G => ?_⟩
  obtain ⟨S, hS, hlo, hgap⟩ := leaf_at_half_slack G
  rw [hval G]
  exact ⟨S, hS, hlo, hgap⟩


/-! ## 3b.  The program for `W/2`, filled: the weakened sentence, unconditionally

The leaf's sentence asks for a poly-time computable `L : Input → ℚ≥0`.  At the relaxed constant
the natural choice is `L := W/2 = Rq/4`, and the shelf already has every piece: `BrickRQ.Rq_poly`
sums the weights off the request encoding, `Poly.rat_div` divides by the constant `4`, and
`AuditM2.tm2_of_nnratPolyProgram` adapts a `ℚ≥0`-valued program to the leaf's `TM2×` shape. -/

section Program

local instance instRequestCodingDirect : OAI.MetricKMedian.Binary.Automatic.Coding
    (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

open OAI.MetricKMedian.Binary

/-- **`Rq/4` is a program at the leaf's request encoder.** -/
noncomputable def RqDivFourProgram : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
    (fun a : QuantumMaxCutEnergy.Input × List Bool => QMCLeafB.EngineRuntime.Rq a.1 / 4) :=
  (Automatic.Poly.comp Automatic.Poly.rat_div
    (Automatic.Poly.pair QMCLeafB.BrickRQ.Rq_poly
      (Automatic.Poly.const (4 : ℚ)))).program

/-- The candidate lower bound `L := W/2 = Rq/4`, as a nonnegative rational. -/
def Lhalf (G : Input) : ℚ≥0 :=
  ⟨QMCLeafB.EngineRuntime.Rq G / 4,
    div_nonneg (QMCLeafB.EngineRuntime.Rq_nonneg G) (by norm_num)⟩

/-- `Rq` is twice the rational total weight. -/
theorem Rq_eq_two_weight (G : Input) :
    QMCLeafB.EngineRuntime.Rq G = 2 * ∑ e : Edge G.n, (G.weights e : ℚ) := by
  rw [QMCLeafB.BrickRQ.Rq_eq_two_edgeWeightSum, QMCNumericRuntime.inputEdges_weight_sum]

/-- `Lhalf` is the total weight halved. -/
theorem Lhalf_val (G : Input) : (Lhalf G : ℝ) = W G / 2 := by
  have h1 : ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) = 2 * W G := by
    rw [Rq_eq_two_weight G]
    push_cast
    rfl
  have h2 : (Lhalf G : ℝ) = ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) / 4 := by
    simp [Lhalf]
  rw [h2, h1]; ring

/-- **`L := W/2` is poly-time computable** in the leaf's own `TM2` sense. -/
theorem Lhalf_tm2 :
    Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
      QuantumMaxCutEnergy.encodeValue
      (fun request : QuantumMaxCutEnergy.Input × List Bool => Lhalf request.1)) := by
  refine QMCLeafB.AuditM2.tm2_of_nnratPolyProgram (f := Lhalf) ?_
  exact RqDivFourProgram.recode id (fun _ => rfl) (fun _ => rfl)

end Program

/-- **The leaf's sentence, proved unconditionally with the slack relaxed to `W/2`.**  Same shape as
`d9f601e5` (same inline weight matrix — here the shelf's `QMCLeafB.wMatrix` — same `ℚ≥0`-valued
poly-time `L`, same `IsMaxcutSDPValue` clause), with `W/2` in place of `W/10000`. -/
theorem leaf_sentence_half_slack_unconditional :
    ∃ L : Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : Input × List Bool => L request.1)) ∧
      ∀ G : Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
          (L G : ℝ) ≤ S ∧ S - (L G : ℝ) ≤ W G / 2 := by
  refine ⟨Lhalf, Lhalf_tm2, fun G => ?_⟩
  obtain ⟨S, hS, hlo, hgap⟩ := leaf_at_half_slack G
  rw [Lhalf_val G]
  exact ⟨S, hS, hlo, hgap⟩

/-! ## 4.  The two witness instances

`Gedge` is the single edge of weight one (`n = 2`), whose SDP value is exactly its total weight
`1`.  `Gtri` is the flat triangle (`n = 3`, weight `1/3` on each edge), whose total weight is also
`1` but whose SDP value is at most `3/4`.  Same total weight, different value: no function of the
total weight can be within `W/10000` of both. -/

/-- The single edge of weight one. -/
abbrev Gedge : Input where
  n := 2
  weights := fun _ => 1

/-- The flat triangle: three edges of weight `1/3`. -/
abbrev Gtri : Input where
  n := 3
  weights := fun _ => 1 / 3

theorem W_Gedge : W Gedge = 1 := by
  have hcard : Fintype.card (Edge 2) = 1 := by decide
  have hsum : W Gedge = ∑ _e : Edge 2, ((1 : ℚ≥0) : ℝ) := rfl
  rw [hsum, Finset.sum_const, Finset.card_univ, hcard]
  norm_num

theorem W_Gtri : W Gtri = 1 := by
  have hcard : Fintype.card (Edge 3) = 3 := by decide
  have hsum : W Gtri = ∑ _e : Edge 3, (((1 / 3 : ℚ≥0) : ℝ)) := rfl
  rw [hsum, Finset.sum_const, Finset.card_univ, hcard]
  norm_num

/-- The weight matrix of the single edge. -/
theorem wMatrix_Gedge :
    QMCLeafB.wMatrix Gedge = !![(0 : ℝ), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QMCLeafB.wMatrix_apply, Gedge]

/-- The primal point `(1, −1)(1, −1)ᵀ` attains the total weight on the single edge. -/
theorem lowerValue_Gedge :
    QMCLeafB.lowerValue (QMCLeafB.wMatrix Gedge) (!![(1 : ℝ), -1; -1, 1]) = 1 := by
  have hV : QMCLeafB.V (QMCLeafB.wMatrix Gedge) = 2 := by
    rw [QMCLeafB.V_wMatrix]
    change 2 * W Gedge = 2
    rw [W_Gedge]; ring
  have htr : (QMCLeafB.wMatrix Gedge * !![(1 : ℝ), -1; -1, 1]).trace = -2 := by
    rw [wMatrix_Gedge, Matrix.mul_fin_two, Matrix.trace_fin_two]
    norm_num
  rw [QMCLeafB.lowerValue, hV, htr]
  norm_num

/-- **The single edge's SDP value is its total weight.** -/
theorem sdpValue_Gedge (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix Gedge) S) : S = 1 := by
  have hEq : (!![(1 : ℝ), -1; -1, 1])
      = Matrix.vecMulVec (fun i : Fin 2 => (![1, -1] : Fin 2 → ℝ) i)
          (fun i : Fin 2 => (![1, -1] : Fin 2 → ℝ) i) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply]
  have hpsd : (!![(1 : ℝ), -1; -1, 1]).PosSemidef := by
    rw [hEq]
    simpa [star_trivial] using
      (Matrix.posSemidef_vecMulVec_self_star (fun i : Fin 2 => (![1, -1] : Fin 2 → ℝ) i))
  have hdiag : ∀ i : Fin 2, (!![(1 : ℝ), -1; -1, 1]) i i = 1 := by
    intro i
    fin_cases i <;> simp
  have hlow := QMCLeafB.le_of_feasible hS hpsd hdiag
  rw [lowerValue_Gedge] at hlow
  have hup := (sdpValue_sandwich Gedge hS).2
  rw [W_Gedge] at hup
  linarith

/-- The dual point `y ≡ 1/3` is feasible for the flat triangle: `diagonal y + A = (1/3)·J`. -/
theorem diag_add_wMatrix_Gtri :
    Matrix.diagonal (fun _ : Fin 3 => ((1 / 3 : ℚ) : ℝ)) + QMCLeafB.wMatrix Gtri
      = (1 / 3 : ℝ) • Matrix.of (fun _ _ : Fin 3 => (1 : ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QMCLeafB.wMatrix_apply, Gtri, Matrix.diagonal, Matrix.one_apply]

/-- `(1/3)·J₃` is positive semidefinite. -/
theorem posSemidef_third_J :
    ((1 / 3 : ℝ) • Matrix.of (fun _ _ : Fin 3 => (1 : ℝ))).PosSemidef := by
  have hJ : Matrix.of (fun _ _ : Fin 3 => (1 : ℝ))
      = Matrix.vecMulVec (fun _ => (1 : ℝ)) (star (fun _ => (1 : ℝ)) : Fin 3 → ℝ) := by
    ext i j
    simp [Matrix.vecMulVec_apply]
  rw [hJ]
  exact Matrix.PosSemidef.smul (Matrix.posSemidef_vecMulVec_self_star _) (by norm_num)

/-- **The flat triangle's SDP value is at most `3/4` of ... exactly `3/4`.** -/
theorem sdpValue_Gtri_le (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix Gtri) S) : S ≤ 3 / 4 := by
  have hy : (Matrix.diagonal (fun _ : Fin 3 => ((1 / 3 : ℚ) : ℝ))
      + QMCLeafB.wMatrix Gtri).PosSemidef := by
    rw [diag_add_wMatrix_Gtri]
    exact posSemidef_third_J
  have h := QMCLeafB.IsMaxcutSDPValue.le_upperValue hS hy
  have hval : QMCLeafB.upperValue (QMCLeafB.wMatrix Gtri)
      (fun _ : Fin 3 => ((1 / 3 : ℚ) : ℝ)) = 3 / 4 := by
    rw [QMCLeafB.upperValue, QMCLeafB.V_wMatrix]
    change (2 * W Gtri + ∑ _i : Fin 3, ((1 / 3 : ℚ) : ℝ)) / 4 = 3 / 4
    rw [W_Gtri]
    simp [Fin.sum_univ_three]
    norm_num
  rwa [hval] at h


/-! ## 4b.  The same obstruction at fixed vertex count

`Gedge`/`Gtri` differ in `n`, so they only rule out functions of the total weight.  The next pair
has the same `n` *and* the same total weight: the flat triangle (value `3/4`) against the path of
two edges of weight `1/2` (value `1`).  No function of `(n, W)` can serve either. -/

/-- The path on three vertices: the edges `01` and `02`, each of weight `1/2`. -/
abbrev Gpath : Input where
  n := 3
  weights := fun e =>
    if e.val = ((0 : Fin 3), (1 : Fin 3)) ∨ e.val = ((0 : Fin 3), (2 : Fin 3))
      then 1 / 2 else 0

/-- The weight matrix of the path. -/
theorem wMatrix_Gpath :
    QMCLeafB.wMatrix Gpath
      = !![(0 : ℝ), 1 / 2, 1 / 2; 1 / 2, 0, 0; 1 / 2, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QMCLeafB.wMatrix_apply, Gpath]

/-- The total weight as half the double sum. -/
theorem W_eq_V (G : Input) : W G = QMCLeafB.V (QMCLeafB.wMatrix G) / 2 := by
  rw [QMCLeafB.V_wMatrix]
  show (∑ e, (G.weights e : ℝ)) = 2 * (∑ e, (G.weights e : ℝ)) / 2
  ring

theorem W_Gpath : W Gpath = 1 := by
  rw [W_eq_V, QMCLeafB.V, wMatrix_Gpath]
  simp [Fin.sum_univ_three]
  norm_num

/-- The sign vector `(1, −1, −1)`. -/
def v3 : Fin 3 → ℝ := ![1, -1, -1]

/-- The rank-one primal point `v vᵀ` at `v = (1, −1, −1)`. -/
def X3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.vecMulVec v3 v3

theorem X3_psd : X3.PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star v3
  simpa [X3, star_trivial] using h

theorem X3_apply (i j : Fin 3) : X3 i j = v3 i * v3 j := by
  rw [X3, Matrix.vecMulVec_apply]

theorem X3_diag : ∀ i : Fin 3, X3 i i = 1 := by
  intro i
  rw [X3, Matrix.vecMulVec_apply]
  fin_cases i <;> simp [v3]

/-- The path's two edges are cut by `(1, −1, −1)`, so the primal value is the total weight. -/
theorem lowerValue_Gpath :
    QMCLeafB.lowerValue (QMCLeafB.wMatrix Gpath) X3 = 1 := by
  have hV : QMCLeafB.V (QMCLeafB.wMatrix Gpath) = 2 := by
    rw [QMCLeafB.V, wMatrix_Gpath]
    simp [Fin.sum_univ_three]
    norm_num
  have htr : (QMCLeafB.wMatrix Gpath * X3).trace = -2 := by
    have htr_eq : (QMCLeafB.wMatrix Gpath * X3).trace
        = ∑ i : Fin 3, ∑ j : Fin 3, QMCLeafB.wMatrix Gpath i j * X3 j i := by
      simp [Matrix.trace, Matrix.mul_apply]
    rw [htr_eq, wMatrix_Gpath]
    simp [X3_apply, v3, Fin.sum_univ_three]
    norm_num
  rw [QMCLeafB.lowerValue, hV, htr]
  norm_num

/-- **The path's SDP value is its total weight.** -/
theorem sdpValue_Gpath (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix Gpath) S) : S = 1 := by
  have hlow := QMCLeafB.le_of_feasible hS X3_psd X3_diag
  rw [lowerValue_Gpath] at hlow
  have hup := (sdpValue_sandwich Gpath hS).2
  rw [W_Gpath] at hup
  linarith

/-- **No `L` that depends only on `(n, total weight)` can prove the leaf.**  The flat triangle and
the path of two half-weight edges have the same vertex count `3` and the same total weight `1`, but
SDP values `3/4` and `1`; the leaf demands agreement to `1/10000`. -/
theorem no_vertexWeight_L (Lw : ℕ → ℝ → ℝ) :
    ¬ (∀ G : Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
          Lw G.n (W G) ≤ S ∧ S - Lw G.n (W G) ≤ W G / 10000) := by
  intro h
  obtain ⟨S₁, hS₁, hle₁, -⟩ := h Gtri
  obtain ⟨S₂, hS₂, -, hgap₂⟩ := h Gpath
  have he₁ : S₁ ≤ 3 / 4 := sdpValue_Gtri_le S₁ hS₁
  have he₂ : S₂ = 1 := sdpValue_Gpath S₂ hS₂
  rw [W_Gtri] at hle₁
  rw [W_Gpath] at hgap₂
  rw [he₂] at hgap₂
  -- both instances have `n = 3` and total weight `1`
  have hn₁ : Gtri.n = 3 := rfl
  have hn₂ : Gpath.n = 3 := rfl
  rw [hn₁] at hle₁
  rw [hn₂] at hgap₂
  have hlow : Lw 3 1 ≤ 3 / 4 := le_trans hle₁ he₁
  have hhigh : (1 : ℝ) - 1 / 10000 ≤ Lw 3 1 := by linarith
  linarith

/-! ## 5.  The why-not: no total-weight proxy can meet the leaf's slack -/

/-- **No `L` that depends only on the total weight can prove the leaf.**

If the leaf's per-instance conclusion held with `L G` a function `Lw (W G)` of the total weight
alone, then `Lw 1` would have to be at least `1 − 1/10000` (from the single edge, whose value is
`1`) and at most `3/4` (from the flat triangle, whose value is at most `3/4`).  Hence every route
to `d9f601e5` must evaluate the graph-dependent SDP value — the residual `hd` is not removable by
any weight-sum proxy. -/
theorem no_totalWeight_L (Lw : ℝ → ℝ) :
    ¬ (∀ G : Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
          Lw (W G) ≤ S ∧ S - Lw (W G) ≤ W G / 10000) := by
  intro h
  obtain ⟨S₁, hS₁, hle₁, hgap₁⟩ := h Gedge
  obtain ⟨S₂, hS₂, hle₂, -⟩ := h Gtri
  have he₁ : S₁ = 1 := sdpValue_Gedge S₁ hS₁
  have he₂ : S₂ ≤ 3 / 4 := sdpValue_Gtri_le S₂ hS₂
  rw [W_Gedge] at hle₁ hgap₁
  rw [W_Gtri] at hle₂
  rw [he₁] at hle₁ hgap₁
  have hlow : (1 : ℝ) - 1 / 10000 ≤ Lw 1 := by linarith
  linarith

/-- The same obstruction, stated with the leaf's own `ℚ≥0`-valued `L` composed with `W`: no
`Lw : ℝ → ℚ≥0` works either. -/
theorem no_totalWeight_L_nnrat (Lw : ℝ → ℚ≥0) :
    ¬ (∀ G : Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
          (Lw (W G) : ℝ) ≤ S ∧ S - (Lw (W G) : ℝ) ≤ W G / 10000) := by
  intro h
  obtain ⟨S₁, hS₁, hle₁, hgap₁⟩ := h Gedge
  obtain ⟨S₂, hS₂, hle₂, -⟩ := h Gtri
  have he₁ : S₁ = 1 := sdpValue_Gedge S₁ hS₁
  have he₂ : S₂ ≤ 3 / 4 := sdpValue_Gtri_le S₂ hS₂
  rw [W_Gedge] at hle₁ hgap₁
  rw [W_Gtri] at hle₂
  rw [he₁] at hle₁ hgap₁
  have hlow : (1 : ℝ) - 1 / 10000 ≤ (Lw 1 : ℝ) := by linarith
  linarith


/-! ## 6.  Repair of the `hgrid1` block of `Check_centre_closure_m4` (d1), in this module

The abandoned file `Solutions/Check_centre_closure_m4.lean` (m4, direction d1) does **not** compile
under this toolchain: its `exists_precision` / `exists_uniform_precision` / `exists_grid_budget`
use the identifiers `Nat.succ_le_two_pow` and `div_le_div_iff`, which do not exist here, and three
of its steps leave unsolved goals (so those three declarations carry `sorryAx`).  What they *assert*
is true and is exactly the precision slot `hgrid1` of the surrogate-centre interface, so it is
re-proved here, hypothesis-for-hypothesis, with the same statements (namespace-local names, so they
can be dropped into `QMCLeafB.CentreClosure` verbatim):

* `exists_dyadic_small` — one dyadic scale meets one positive budget (`pow_unbounded_of_one_lt`,
  Archimedean, instead of the absent `Nat.succ_le_two_pow`);
* `exists_uniform_precision` — one scale meets finitely many positive budgets (min over `k < K`);
* `exists_grid_budget` — the bracket width `invSqrtGe − invSqrtLe ≤ 2^{-G}`
  (`DQ.invSqrt_width_le_of_one_le`) times the accumulated `∑_{j<k} γ_j b_{k j}` is at most
  `marg k / 2` for every `k < K` at one uniform `G`.

These are the *only* three declarations of m4's file that fail; `hbody_of_trace`,
`hstatec_at_surrogate`, `runParts_shallow_surrogate` and the rest of its 24 compile and audit clean. -/

/-- For `S ≥ 0` and `marg > 0` some dyadic scale makes `S / 2^G ≤ marg / 2`. -/
theorem exists_dyadic_small {S marg : ℚ} (hS : 0 ≤ S) (hm : 0 < marg) :
    ∃ G : ℕ, S / 2 ^ G ≤ marg / 2 := by
  obtain ⟨G, hG⟩ := pow_unbounded_of_one_lt (2 * S / marg) (by norm_num : (1 : ℚ) < 2)
  refine ⟨G, ?_⟩
  have hpow : (0 : ℚ) < 2 ^ G := by positivity
  have h3 : 2 * S < marg * 2 ^ G := by
    rw [div_lt_iff₀ hm] at hG
    linarith
  rw [div_le_iff₀ hpow]
  linarith

/-- One precision meets finitely many positive budgets. -/
theorem exists_uniform_precision (K : ℕ) (S : ℚ) (hS : 0 ≤ S) (marg : ℕ → ℚ)
    (hm : ∀ k, 0 < marg k) :
    ∃ G : ℕ, ∀ k, k < K → S / 2 ^ G ≤ marg k / 2 := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · exact ⟨0, fun k hk => absurd hk (by omega)⟩
  · have hne : (Finset.range K).Nonempty := ⟨0, Finset.mem_range.mpr hK⟩
    obtain ⟨k0, _hk0, hmin⟩ := Finset.exists_min_image (Finset.range K) marg hne
    obtain ⟨G, hG⟩ := exists_dyadic_small hS (hm k0)
    refine ⟨G, fun k hk => ?_⟩
    refine le_trans hG ?_
    have h1 : marg k0 ≤ marg k := hmin k (Finset.mem_range.mpr hk)
    linarith

/-- The dyadic grid budget of the surrogate centre: one precision `G` meets every `marg k`. -/
theorem exists_grid_budget (K : ℕ) (γ : ℕ → ℚ) (b : ℕ → ℕ → ℚ) (σ : ℕ → ℚ) (marg : ℕ → ℚ)
    (hγ : ∀ j, 0 ≤ γ j) (hb : ∀ k j, 0 ≤ b k j) (hσ : ∀ j, 1 ≤ σ j) (hm : ∀ k, 0 < marg k) :
    ∃ G : ℕ, ∀ k, k < K →
      ∑ j ∈ Finset.range k,
          γ j * (DQ.invSqrtGe (σ j) G - DQ.invSqrtLe (σ j) G) * b k j
        ≤ marg k / 2 := by
  classical
  set S : ℚ := ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range k, γ j * b k j with hSdef
  have hS0 : (0 : ℚ) ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (hγ j) (hb k j)
  obtain ⟨G, hG⟩ := exists_uniform_precision K S hS0 marg hm
  refine ⟨G, fun k hk => ?_⟩
  have hw : ∀ j, DQ.invSqrtGe (σ j) G - DQ.invSqrtLe (σ j) G ≤ 1 / 2 ^ G :=
    fun j => DQ.invSqrt_width_le_of_one_le (hσ j) G
  have hwid : (0 : ℚ) ≤ 1 / 2 ^ G := by positivity
  have hstep1 : ∑ j ∈ Finset.range k,
        γ j * (DQ.invSqrtGe (σ j) G - DQ.invSqrtLe (σ j) G) * b k j
      ≤ ∑ j ∈ Finset.range k, γ j * (1 / 2 ^ G) * b k j := by
    refine Finset.sum_le_sum fun j _ => ?_
    have h2 := hw j
    have h3 : 0 ≤ γ j * b k j := mul_nonneg (hγ j) (hb k j)
    nlinarith [h2, h3]
  have hstep2 : ∑ j ∈ Finset.range k, γ j * (1 / 2 ^ G) * b k j
      = (1 / 2 ^ G) * (∑ j ∈ Finset.range k, γ j * b k j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hstep3 : (1 / 2 ^ G) * (∑ j ∈ Finset.range k, γ j * b k j) ≤ (1 / 2 ^ G) * S := by
    refine mul_le_mul_of_nonneg_left ?_ hwid
    rw [hSdef]
    exact Finset.single_le_sum (f := fun k => ∑ j ∈ Finset.range k, γ j * b k j)
      (fun k _ => Finset.sum_nonneg fun j _ => mul_nonneg (hγ j) (hb k j))
      (Finset.mem_range.mpr hk)
  have hstep4 : (1 / 2 ^ G) * S = S / 2 ^ G := by ring
  have hfin : S / 2 ^ G ≤ marg k / 2 := hG k hk
  linarith


/-! ## Axiom audit -/

#print axioms QMCLeafB.Direct.weightMatrix_eq_wMatrix
#print axioms QMCLeafB.Direct.exists_sdpValue
#print axioms QMCLeafB.Direct.sdpValue_sandwich
#print axioms QMCLeafB.Direct.leaf_at_half_slack
#print axioms QMCLeafB.Direct.leaf_at_scaled_slack
#print axioms QMCLeafB.Direct.leaf_sentence_half_slack
#print axioms QMCLeafB.Direct.RqDivFourProgram
#print axioms QMCLeafB.Direct.Rq_eq_two_weight
#print axioms QMCLeafB.Direct.Lhalf_val
#print axioms QMCLeafB.Direct.Lhalf_tm2
#print axioms QMCLeafB.Direct.leaf_sentence_half_slack_unconditional
#print axioms QMCLeafB.Direct.W_Gedge
#print axioms QMCLeafB.Direct.W_Gtri
#print axioms QMCLeafB.Direct.wMatrix_Gedge
#print axioms QMCLeafB.Direct.lowerValue_Gedge
#print axioms QMCLeafB.Direct.sdpValue_Gedge
#print axioms QMCLeafB.Direct.diag_add_wMatrix_Gtri
#print axioms QMCLeafB.Direct.posSemidef_third_J
#print axioms QMCLeafB.Direct.sdpValue_Gtri_le
#print axioms QMCLeafB.Direct.wMatrix_Gpath
#print axioms QMCLeafB.Direct.W_Gpath
#print axioms QMCLeafB.Direct.X3_psd
#print axioms QMCLeafB.Direct.X3_diag
#print axioms QMCLeafB.Direct.lowerValue_Gpath
#print axioms QMCLeafB.Direct.sdpValue_Gpath
#print axioms QMCLeafB.Direct.no_vertexWeight_L
#print axioms QMCLeafB.Direct.no_totalWeight_L
#print axioms QMCLeafB.Direct.wMatrix_Gpath
#print axioms QMCLeafB.Direct.W_Gpath
#print axioms QMCLeafB.Direct.X3_psd
#print axioms QMCLeafB.Direct.X3_diag
#print axioms QMCLeafB.Direct.lowerValue_Gpath
#print axioms QMCLeafB.Direct.sdpValue_Gpath
#print axioms QMCLeafB.Direct.no_vertexWeight_L
#print axioms QMCLeafB.Direct.no_totalWeight_L_nnrat
#print axioms QMCLeafB.Direct.exists_dyadic_small
#print axioms QMCLeafB.Direct.exists_uniform_precision
#print axioms QMCLeafB.Direct.exists_grid_budget

end QMCLeafB.Direct


