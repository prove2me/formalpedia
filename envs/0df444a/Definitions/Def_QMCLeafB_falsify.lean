-- Prove2me | Definitions.Def_QMCLeafB_falsify
-- name    : QMCLeafB_falsify
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:06:05.689242+00:00
-- url     : https://prove2.me/theorems/07dc39aa-08b3-4575-9d99-7b86ec57b715
-- title:
--   QMCLeafB falsify
-- statement:
--   # leaf B phase 19 — brick `falsify` (swarm `smw1k12jb`, member m1, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_closingAssembly_m3
import Definitions.Def_QMCLeafB_triobstruction_m5
import Definitions.Def_QMCLeafB_inhabit_m5
/-
# leaf B phase 19 — brick `falsify` (swarm `smw1k12jb`, member m1, direction d4)

The closing assembly (`Check_closingAssembly_m3`) reduces the leaf `d9f601e5` to one residual,
`Resid o Pfam` — one `Bundle` per interior `(G, t)`.  This file is the **adversarial audit** of that
reduction.  It proves nothing about the leaf; it pins down what the reduction does and does not
claim, so that a supplier cannot close it by accident:

* §1 **statement lock** — the closing's conclusion `QMCLeafB.FinishLine.SolutionStatement` is
  *definitionally* the verbatim `d9f601e5` sentence (`statement_lock : … ↔ VerbatimTarget`, by
  `Iff.rfl`).  So `ClosingAssembly.solution` proves the target and not a paraphrase of it.
* §2 **the residual's domain is not empty** — at the one-edge instance `Gtwo` the interior bracket
  is inhabited (`t = -Rq`), so `Resid` is a genuine obligation at a named input, and applying it
  there produces a `Bundle` (not an empty `∀`).
* §3 **the flag stream is a choice, the verdict is not** — `Bundle.hokAll` with `ok ≡ false` is
  free data; what binds is `hverdict : o G t = anyOk ok (K·m)`, i.e. the campaign's own output bit
  must be `false` throughout the interior bracket.  At the triangle's lower half that premise is
  *derivable* (every round must answer `cut`, from the trace floor), so the all-`false` stream is
  consistent there; at `Gtwo` it is not derivable and not contradicted — the slot is load-bearing.
* §4 **the empty-body shortcut does not cover the bracket** — at the triangle below `-Rq/2` the
  relaxed body is empty and the whole `RelaxCut` record is free (`relaxCut_of_empty`); at `Gtwo`
  the pinch point `(1 - dq/4) • Q₀` is *in* the body for every `t ≥ -Rq + eps`, so on all but an
  `eps`-sliver of the bracket the cut records must be genuine separations, not vacuity.
* §5 **`hTrc` is a real constraint** — it fails at the identity centre and is attained with
  equality at the pinch, so it can neither be dropped nor satisfied by an arbitrary centre.
* §6 **axiom cone** — every theorem of the closing chain and of this file audits to
  `[propext, Classical.choice, Quot.sound]`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.FalsifyM1

open QuantumMaxCutEnergy

/-! ## 1.  Statement lock

`Check_brick_finish_line.solutionStatement_iff_wMatrix` locks the `wMatrix` paraphrase of the
sentence.  The stronger fact — that `SolutionStatement` *is* the `d9f601e5` sentence, quotation
mark for quotation mark — is the one the leaf needs, and it is a definitional equality: -/

/-- The `d9f601e5` target, transcribed from the problem statement. -/
def VerbatimTarget : Prop :=
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

/-- **The closing proves the target.**  `SolutionStatement` and the verbatim `d9f601e5` sentence are
the same proposition; the proof is `Iff.rfl`, i.e. Lean's definitional equality checker. -/
theorem statement_lock : QMCLeafB.FinishLine.SolutionStatement ↔ VerbatimTarget :=
  Iff.rfl

#print axioms QMCLeafB.FalsifyM1.statement_lock

/-- The closing's own conclusion, read at the verbatim statement. -/
theorem verbatim_of_solutionStatement (h : QMCLeafB.FinishLine.SolutionStatement) :
    VerbatimTarget :=
  statement_lock.mp h

#print axioms QMCLeafB.FalsifyM1.verbatim_of_solutionStatement

/-! ## 2.  The residual's domain is inhabited at a named input

`Resid` quantifies over `(G, t)` with `2 ≤ G.n` and `t` in the interior bracket.  If that bracket
were empty at every `G`, `Resid` would be a vacuous `∀` and the reduction would prove nothing.  It
is empty exactly when `Rq G = 0` (`ClosingAssembly.resid_range_nonempty_iff`); here is the concrete
positive case. -/

/-- **The interior bracket at the one-edge instance is inhabited** (`Rq Gtwo = 2`, `t = -2`). -/
theorem bracket_at_Gtwo :
    ∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq QMCLeafB.InhabitM5.Gtwo ≤ t ∧
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.InhabitM5.Gtwo / 40000 : ℚ)) : ℝ) := by
  refine ⟨-2, ?_, ?_⟩
  · rw [QMCLeafB.InhabitM5.Rq_Gtwo]
  · rw [QMCLeafB.InhabitM5.Rq_Gtwo]
    norm_num

#print axioms QMCLeafB.FalsifyM1.bracket_at_Gtwo

/-- **The same at the triangle** (`Rq Gtri = 6`, `t = -6`). -/
theorem bracket_at_Gtri :
    ∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq QMCLeafB.TriObstructionM5.Gtri ≤ t ∧
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.TriObstructionM5.Gtri / 40000 : ℚ)) : ℝ) := by
  refine ⟨-6, ?_, ?_⟩
  · rw [QMCLeafB.TriObstructionM5.Rq_Gtri]
  · rw [QMCLeafB.TriObstructionM5.Rq_Gtri]
    norm_num

#print axioms QMCLeafB.FalsifyM1.bracket_at_Gtri

/-- **`Resid` is applied, not merely stated.**  A supplier of the residual owes a `Bundle` at the
one-edge instance and the bottom of its bracket; this is that obligation, extracted. -/
def resid_forces_bundle_Gtwo
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (h : QMCLeafB.ClosingAssembly.Resid o P) :
    QMCLeafB.ClosingAssembly.Bundle o QMCLeafB.InhabitM5.Gtwo (-2)
      (P QMCLeafB.InhabitM5.Gtwo) (by decide) :=
  h _ (-2) (by decide) (by rw [QMCLeafB.InhabitM5.Rq_Gtwo]) (by
    rw [QMCLeafB.InhabitM5.Rq_Gtwo]; norm_num)

#print axioms QMCLeafB.FalsifyM1.resid_forces_bundle_Gtwo



/-! ## 3.  The flag stream is a choice; the verdict bit is not

`Bundle.hokAll` is *data*: taking `ok := fun _ => false` makes it `rfl`.  What a supplier cannot
choose is `Bundle.hverdict`, which equates the campaign's own output bit with `anyOk ok (K·m)`.  On
an all-`false` stream that reads `o G t = false` (`verdict_eq_false_of_allFalse`), so the residual
demands that the campaign answers `cut` at *every* interior `(G, t)`.

At the triangle that demand is not an assumption but a theorem — every round below the trace floor
must answer `cut`, because an `ok` round would have to exhibit a unit-diagonal PSD point under
`t + eps < -3`, and none exists.  So the all-`false` stream is consistent there. -/

/-- **Every round at the triangle's lower half answers `cut`.**  The `ok` certificate is ruled out
by the trace floor `trace_ge`, so the flag stream of *any* run in that range is all-`false`. -/
theorem ok_false_at_Gtri (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (t : ℚ)
    (ht : (t : ℝ)
      + ((QMCLeafB.RundataCert.eps QMCLeafB.TriObstructionM5.Gtri : ℚ) : ℝ) < -3)
    (B : QMCLeafB.FinalStroke.RunParts o QMCLeafB.TriObstructionM5.Gtri t
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.TriObstructionM5.Gtri))
    (k : ℕ) (hk : k < (QMCLeafB.UnionShallow.paramsKbc2
      QMCLeafB.TriObstructionM5.Gtri).K
      * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.TriObstructionM5.Gtri).m) :
    B.ok k = false := by
  rcases Bool.eq_false_or_eq_true (B.ok k) with h | h
  · exfalso
    obtain ⟨X, hX, hle⟩ := B.hcert k hk h
    refine QMCLeafB.TriObstructionM5.no_ok_cert_below t ht X hX ?_
    unfold QMCLeafB.RundataCert.eps at *
    exact hle
  · exact h

#print axioms QMCLeafB.FalsifyM1.ok_false_at_Gtri

/-- **The bundle's flag clause is consistent at the triangle**: from any `Bundle` there, the
campaign's bit is `false` (`verdict_eq_false_of_allFalse`), and *independently* every run at that
threshold has all-`false` flags (`ok_false_at_Gtri`).  The two agree, so the all-`false` demand is
not an artefact of the bundle's phrasing. -/
theorem bundle_bit_false_Gtri {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams QMCLeafB.TriObstructionM5.Gtri}
    {hn : 2 ≤ QMCLeafB.TriObstructionM5.Gtri.n}
    (B : QMCLeafB.ClosingAssembly.Bundle o QMCLeafB.TriObstructionM5.Gtri t P hn) :
    o QMCLeafB.TriObstructionM5.Gtri t = false :=
  QMCLeafB.ClosingAssembly.verdict_eq_false_of_allFalse B

#print axioms QMCLeafB.FalsifyM1.bundle_bit_false_Gtri





/-! ## 4.  The empty-body shortcut covers the triangle, not the one-edge interior

`Check_triobstruction_m5.relaxCut_of_empty`: if the relaxed body `relaxBodyLE A (t - eps) δ` is
empty then *every* rational centre carries a `RelaxCut` record (normal `1`, margin `1`) — the
cut-record slot of the bundle for free.  That is a genuine route at the triangle's lower half, where
the body is empty (`relaxCut_Gtri_below`).

It is **not** a general route.  At the one-edge instance the pinch point `(1 - dq/4) • Q₀` lies in
the body for every `t ≥ -Rq + eps`, i.e. on all of the interior bracket except the `eps`-sliver at
its bottom.  So on that range the vacuity hypothesis fails and the `RelaxCut` records of the bundle
must be genuine separations.  This is the machine-checked form of the phase-18 warning that the
program's cuts are its true violated directions. -/

/-- The campaign tolerance at the one-edge instance. -/
abbrev dqTwo : ℚ := (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.InhabitM5.Gtwo).dq

theorem dqTwo_pos : 0 < dqTwo := QMCLeafB.InhabitM5.dq_Gtwo_pos

theorem dqTwo_le_four : dqTwo ≤ 4 := QMCLeafB.InhabitM5.dq_Gtwo_le_four

/-- The pinch point, in `ℝ`: `(1 - dq/4) • Q₀`. -/
def pinchTwo : Matrix (Fin QMCLeafB.InhabitM5.Gtwo.n)
    (Fin QMCLeafB.InhabitM5.Gtwo.n) ℝ :=
  QMCLeafB.SepOracle.castMat ((1 - dqTwo / 4) • QMCLeafB.InhabitM5.Q0)

/-- A two-term sum at the two-vertex index type (cf. `InhabitM5.sum_inst`). -/
theorem sum2 {M : Type} [AddCommMonoid M] (f : Fin QMCLeafB.InhabitM5.Gtwo.n → M) :
    ∑ i, f i = f 0 + f 1 := by
  show (∑ i : Fin 2, f i) = f 0 + f 1
  exact Fin.sum_univ_two f

/-- The diagonal of the pinch point. -/
theorem pinchTwo_diag (i : Fin QMCLeafB.InhabitM5.Gtwo.n) :
    pinchTwo i i = 1 - (dqTwo : ℝ) / 4 := by
  simp only [pinchTwo, QMCLeafB.SepOracle.castMat_apply, Matrix.smul_apply,
    QMCLeafB.InhabitM5.Q0_diag i, smul_eq_mul, mul_one]
  push_cast
  ring

theorem pinchTwo_off_01 :
    pinchTwo (0 : Fin QMCLeafB.InhabitM5.Gtwo.n) (1 : Fin QMCLeafB.InhabitM5.Gtwo.n)
      = -(1 - (dqTwo : ℝ) / 4) := by
  simp only [pinchTwo, QMCLeafB.SepOracle.castMat_apply, Matrix.smul_apply,
    QMCLeafB.InhabitM5.Q0_01, smul_eq_mul]
  push_cast
  ring

theorem pinchTwo_off_10 :
    pinchTwo (1 : Fin QMCLeafB.InhabitM5.Gtwo.n) (0 : Fin QMCLeafB.InhabitM5.Gtwo.n)
      = -(1 - (dqTwo : ℝ) / 4) := by
  simp only [pinchTwo, QMCLeafB.SepOracle.castMat_apply, Matrix.smul_apply,
    QMCLeafB.InhabitM5.Q0_10, smul_eq_mul]
  push_cast
  ring

/-- The engine's weight matrix at the one-edge instance, in `ℝ`. -/
theorem castMat_wQ_Gtwo_00 :
    QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ QMCLeafB.InhabitM5.Gtwo)
      (0 : Fin QMCLeafB.InhabitM5.Gtwo.n) (0 : Fin QMCLeafB.InhabitM5.Gtwo.n) = 0 := by
  rw [QMCLeafB.SepOracle.castMat_apply, QMCLeafB.InhabitM5.wG_two_00]
  norm_num

theorem castMat_wQ_Gtwo_01 :
    QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ QMCLeafB.InhabitM5.Gtwo)
      (0 : Fin QMCLeafB.InhabitM5.Gtwo.n) (1 : Fin QMCLeafB.InhabitM5.Gtwo.n) = 1 := by
  rw [QMCLeafB.SepOracle.castMat_apply, QMCLeafB.InhabitM5.wG_two_01]
  norm_num

theorem castMat_wQ_Gtwo_10 :
    QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ QMCLeafB.InhabitM5.Gtwo)
      (1 : Fin QMCLeafB.InhabitM5.Gtwo.n) (0 : Fin QMCLeafB.InhabitM5.Gtwo.n) = 1 := by
  rw [QMCLeafB.SepOracle.castMat_apply, QMCLeafB.InhabitM5.wG_two_10]
  norm_num

theorem castMat_wQ_Gtwo_11 :
    QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ QMCLeafB.InhabitM5.Gtwo)
      (1 : Fin QMCLeafB.InhabitM5.Gtwo.n) (1 : Fin QMCLeafB.InhabitM5.Gtwo.n) = 0 := by
  rw [QMCLeafB.SepOracle.castMat_apply, QMCLeafB.InhabitM5.wG_two_11]
  norm_num

/-- `frob` on a two-vertex block, expanded. -/
theorem frob_two (C X : Matrix (Fin QMCLeafB.InhabitM5.Gtwo.n)
    (Fin QMCLeafB.InhabitM5.Gtwo.n) ℝ) :
    QMCLeafB.BallFloor.frob C X
      = C 0 0 * X 0 0 + C 0 1 * X 0 1 + C 1 0 * X 1 0 + C 1 1 * X 1 1 := by
  simp only [QMCLeafB.BallFloor.frob]
  rw [sum2, sum2, sum2]
  ring

/-- The pairing of the one-edge weight matrix with the pinch point: `-2·(1 - dq/4)`. -/
theorem frob_pinchTwo :
    QMCLeafB.BallFloor.frob
        (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ QMCLeafB.InhabitM5.Gtwo))
        pinchTwo
      = -2 * (1 - (dqTwo : ℝ) / 4) := by
  rw [frob_two, castMat_wQ_Gtwo_00, castMat_wQ_Gtwo_01, castMat_wQ_Gtwo_10,
    castMat_wQ_Gtwo_11, pinchTwo_diag, pinchTwo_off_01, pinchTwo_off_10, pinchTwo_diag]
  ring

/-- The quadratic form of the pinch point at a real vector: `(1 - dq/4)·(x₀ - x₁)²`. -/
theorem qfR_pinchTwo (x : Fin QMCLeafB.InhabitM5.Gtwo.n → ℝ) :
    QMCLeafB.BallFloor.qfR pinchTwo x
      = (1 - (dqTwo : ℝ) / 4) * (x 0 - x 1) ^ 2 := by
  simp only [QMCLeafB.BallFloor.qfR, dotProduct, Matrix.mulVec]
  rw [sum2, sum2, sum2, pinchTwo_diag, pinchTwo_off_01, pinchTwo_off_10, pinchTwo_diag]
  ring

/-- **The pinch point is in the relaxed body of the one-edge interior.**  For every threshold at or
above `-Rq + eps`, the relaxed body at `(t - eps, dq)` contains `(1 - dq/4) • Q₀`.  Hence the body
is *not* empty there, and `relaxCut_of_empty` cannot supply the cut records. -/
theorem body_nonempty_Gtwo (t : ℚ)
    (ht : -QMCLeafB.EngineRuntime.Rq QMCLeafB.InhabitM5.Gtwo
        + QMCLeafB.RundataCert.eps QMCLeafB.InhabitM5.Gtwo ≤ t) :
    QMCLeafB.BallFloor.relaxBodyLE
      (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ QMCLeafB.InhabitM5.Gtwo))
      ((t - QMCLeafB.RundataCert.eps QMCLeafB.InhabitM5.Gtwo : ℚ) : ℝ)
      ((dqTwo : ℚ) : ℝ) pinchTwo := by
  have hdqp : (0 : ℝ) < (dqTwo : ℝ) := by exact_mod_cast dqTwo_pos
  have hc0 : (0 : ℝ) ≤ 1 - (dqTwo : ℝ) / 4 := by
    have h4 : (dqTwo : ℝ) ≤ 4 := by exact_mod_cast dqTwo_le_four
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [qfR_pinchTwo]
    have hsq : (0 : ℝ) ≤ (x 0 - x 1) ^ 2 := sq_nonneg _
    have hnn : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [mul_nonneg hc0 hsq]
  · intro i
    rw [pinchTwo_diag i]
    have key : (1 - (dqTwo : ℝ) / 4) - 1 = -(dqTwo / 4) := by ring
    rw [key, abs_of_nonpos (by linarith : -(dqTwo / 4 : ℝ) ≤ 0)]
    ring_nf
    exact le_refl _
  · rw [frob_pinchTwo]
    have hRq : QMCLeafB.EngineRuntime.Rq QMCLeafB.InhabitM5.Gtwo = 2 :=
      QMCLeafB.InhabitM5.Rq_Gtwo
    have ht' : (-2 : ℚ) + QMCLeafB.RundataCert.eps QMCLeafB.InhabitM5.Gtwo ≤ t := by
      rw [hRq] at ht; exact ht
    have hle : (-2 : ℝ) ≤ (t : ℝ)
        - ((QMCLeafB.RundataCert.eps QMCLeafB.InhabitM5.Gtwo : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).2 ht'
      push_cast at h
      linarith
    have hcast : (((t - QMCLeafB.RundataCert.eps QMCLeafB.InhabitM5.Gtwo : ℚ)) : ℝ)
        = (t : ℝ) - ((QMCLeafB.RundataCert.eps QMCLeafB.InhabitM5.Gtwo : ℚ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    nlinarith [hle]

#print axioms QMCLeafB.FalsifyM1.body_nonempty_Gtwo

/-- **The vacuity shortcut fails on the one-edge interior.**  Above the `eps`-sliver the empty-body
hypothesis of `relaxCut_of_empty` is false at `Gtwo`: a point of the relaxation lies in the body, so
the `RelaxCut` records of a `Bundle` there cannot be manufactured by emptiness. -/
theorem not_empty_body_Gtwo (t : ℚ)
    (ht : -QMCLeafB.EngineRuntime.Rq QMCLeafB.InhabitM5.Gtwo
        + QMCLeafB.RundataCert.eps QMCLeafB.InhabitM5.Gtwo ≤ t) :
    ¬ (∀ X : Matrix (Fin QMCLeafB.InhabitM5.Gtwo.n)
          (Fin QMCLeafB.InhabitM5.Gtwo.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE
          (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ QMCLeafB.InhabitM5.Gtwo))
          ((t - QMCLeafB.RundataCert.eps QMCLeafB.InhabitM5.Gtwo : ℚ) : ℝ)
          ((dqTwo : ℚ) : ℝ) X) := by
  intro hempty
  exact hempty pinchTwo (body_nonempty_Gtwo t ht)

#print axioms QMCLeafB.FalsifyM1.not_empty_body_Gtwo

/-- **… while at the triangle it holds.**  The same shortcut *is* available at the triangle's lower
half — the two instances mark the boundary of the vacuity route. -/
theorem frame_Gtri_cut_free (t : ℚ)
    (ht : ((t - QMCLeafB.RundataCert.eps QMCLeafB.TriObstructionM5.Gtri : ℚ) : ℝ)
        + (((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.TriObstructionM5.Gtri).dq : ℚ) : ℝ) / 2
      < -3 - 9 * (((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.TriObstructionM5.Gtri).dq : ℚ) : ℝ)
        / 4)
    (cX : Matrix (Fin QMCLeafB.TriObstructionM5.Gtri.n)
      (Fin QMCLeafB.TriObstructionM5.Gtri.n) ℚ) :
    Nonempty (QMCLeafB.RelaxOracle.RelaxCut
      (QMCLeafB.Finalization.wMatrixQ QMCLeafB.TriObstructionM5.Gtri) cX
      (t - QMCLeafB.RundataCert.eps QMCLeafB.TriObstructionM5.Gtri)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.TriObstructionM5.Gtri).dq) :=
  QMCLeafB.TriObstructionM5.relaxCut_Gtri_below t ht cX

#print axioms QMCLeafB.FalsifyM1.frame_Gtri_cut_free


/-! ## 5.  `hTrc` is a real constraint, and it is attainable

The bundle's trace slot `∑ i, (cX k) i i ≤ n·(1 - dq/4)` is the phase-17 pinch's bookkeeping
(`Check_obstruction_m1`): it is *not* implied by `RelaxMem.diag_near` pointwise, and it is not free.
Two witnesses fix its meaning — it fails at the identity centre, and it is attained with equality
at the pinch, which is exactly why the pinch is the campaign's centre. -/

/-- The trace of the identity centre. -/
theorem trace_one_Gtwo :
    (∑ i, (1 : Matrix (Fin QMCLeafB.InhabitM5.Gtwo.n)
      (Fin QMCLeafB.InhabitM5.Gtwo.n) ℚ) i i) = (QMCLeafB.InhabitM5.Gtwo.n : ℚ) := by
  simp

/-- **The trace budget fails at the identity centre**: `n > n·(1 - dq/4)` for `dq > 0`.  So `hTrc`
is a genuine restriction on which centres a `Bundle` may use; it cannot be discharged by taking the
canonical unit-diagonal point. -/
theorem hTrc_fails_identity_Gtwo :
    ¬ (∑ i, (1 : Matrix (Fin QMCLeafB.InhabitM5.Gtwo.n)
        (Fin QMCLeafB.InhabitM5.Gtwo.n) ℚ) i i
      ≤ (QMCLeafB.InhabitM5.Gtwo.n : ℚ) * (1 - dqTwo / 4)) := by
  have hn : (0 : ℚ) < (QMCLeafB.InhabitM5.Gtwo.n : ℚ) := by
    have : (0 : ℕ) < QMCLeafB.InhabitM5.Gtwo.n := by decide
    exact_mod_cast this
  intro h
  rw [trace_one_Gtwo] at h
  have hlt : (QMCLeafB.InhabitM5.Gtwo.n : ℚ) * (1 - dqTwo / 4)
      < (QMCLeafB.InhabitM5.Gtwo.n : ℚ) := by nlinarith [dqTwo_pos]
  linarith

#print axioms QMCLeafB.FalsifyM1.hTrc_fails_identity_Gtwo

/-- **… and it is attained at the pinch**, with equality — the phase-18 `(1 - dq/4)` boundary is not
an estimate but the exact feasible value. -/
theorem hTrc_attained_Gtwo :
    ∑ i, QMCLeafB.InhabitM5.cXtwo 0 i i
      ≤ (QMCLeafB.InhabitM5.Gtwo.n : ℚ) * (1 - dqTwo / 4) :=
  QMCLeafB.InhabitM5.hTrc_Gtwo 0

#print axioms QMCLeafB.FalsifyM1.hTrc_attained_Gtwo

/-- **The pinch's diagonal is the boundary, not merely inside it.** -/
theorem pinchTwo_diag_eq :
    pinchTwo (0 : Fin QMCLeafB.InhabitM5.Gtwo.n) (0 : Fin QMCLeafB.InhabitM5.Gtwo.n)
      = 1 - (dqTwo : ℝ) / 4 :=
  pinchTwo_diag 0

#print axioms QMCLeafB.FalsifyM1.pinchTwo_diag_eq

/-! ## 6.  Axiom audit of the closing chain

The whole reduction is standard-axiom only: no `sorryAx`, no user `axiom`, nothing classical beyond
`propext`/`Classical.choice`/`Quot.sound`.  Every theorem cited by the closing assembly, and every
stroke it applies, is audited here. -/

#print axioms QMCLeafB.ClosingAssembly.noMem_of_allFalse
#print axioms QMCLeafB.ClosingAssembly.runParts_of_bundle
#print axioms QMCLeafB.ClosingAssembly.rmaxOf_pos
#print axioms QMCLeafB.ClosingAssembly.rmaxOf_le_one
#print axioms QMCLeafB.ClosingAssembly.budget_dqShallow
#print axioms QMCLeafB.ClosingAssembly.hd_of_resid
#print axioms QMCLeafB.ClosingAssembly.solution_statement
#print axioms QMCLeafB.ClosingAssembly.solution
#print axioms QMCLeafB.ClosingAssembly.hdGT_of_resid
#print axioms QMCLeafB.ClosingAssembly.solution_guardT
#print axioms QMCLeafB.ClosingAssembly.verdict_eq_false_of_allFalse
#print axioms QMCLeafB.ClosingAssembly.resid_range_nonempty_iff
#print axioms QMCLeafB.GuardT.solution_of_leaf_guardT
#print axioms QMCLeafB.GuardT.endgame_guardT
#print axioms QMCLeafB.AssemblyM5.endgame_of_hd
#print axioms QMCLeafB.AssemblyM5.endgame_of_hd_statement
#print axioms QMCLeafB.AssemblyM5.endgame_of_hd_pos
#print axioms QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket
#print axioms QMCLeafB.TriObstructionM5.no_true_verdict_half
#print axioms QMCLeafB.TriObstructionM5.relaxCut_Gtri_below
#print axioms QMCLeafB.InhabitM5.residual_inhabited_interior
#print axioms QMCLeafB.InhabitM5.nonempty_runParts_okTrue

/-! ## 7.  What this file does **not** claim

* It does not prove `Resid`, and therefore does not prove the leaf.  `ClosingAssembly.solution`
  still takes `Resid` as a hypothesis, and §2 shows that hypothesis is applied at a concrete input —
  it is not an empty quantifier.
* §3 derives the all-`false` flag stream only at the *triangle's lower half*.  At the one-edge
  instance the two branches are both live: `InhabitM5.residual_inhabited_interior` inhabits
  `RunParts` there with verdict bit `true`, while any `Bundle` forces the bit `false`.  Nothing
  compiled pins the campaign program's own bit at `Gtwo`, so the interior `cut` premise is cited,
  not proved, at `n = 2`.
* §4 kills the empty-body route for the cut records above the `eps`-sliver at `Gtwo`; it does not
  construct the genuine separations that would replace it. -/
end QMCLeafB.FalsifyM1


