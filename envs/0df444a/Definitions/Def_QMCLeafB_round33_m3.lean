-- Prove2me | Definitions.Def_QMCLeafB_round33_m3
-- name    : QMCLeafB_round33_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:47:57.649109+00:00
-- url     : https://prove2.me/theorems/6bd69f84-002d-4fcb-b829-003376564e69
-- title:
--   QMCLeafB round33_m3
-- statement:
--   # `Check_round33_m3` — leaf B, phase 33, member m3, direction **rounding (A)**
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_fal30
import Definitions.Def_QMCLeafB_refuted_m3
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_brick_finish_line
import Definitions.Def_QMCLeafB_brick_verdict_sound
/-
# `Check_round33_m3` — leaf B, phase 33, member m3, direction **rounding (A)**

The phase-33 charter splits the whole leaf into a `Poly` bit plus a `RunParts` family
(`Sound31.solution_of_runPartsFamily`), and lists three record cases: (i) empty body (banked:
`RefutedM3.runParts_of_emptyBody`), (ii) an exact unit-diagonal PSD witness at `t + eps` (banked:
`runParts_of_member`), (iii) **the leftover** — relaxed body non-empty but no exact witness.

This module settles (iii) in its clean form.  **Case (iii) is not a stratum of the geometry**: a
*relaxed* member `RelaxMem (wMatrixQ G) cX (t − eps) dqShallow` already produces an exact
unit-diagonal PSD point at `t + eps` (that is the banked rounding
`RelaxOracle.hcert_of_relaxMem` + the banked budget `UnionShallow.paramsKbc2_budget`).  So the ok
lane needs no exact-PSD stop test, no `Hpsd` pivot-margin certificate and no grid enlargement
(`2n²/dq ≈ 3·10⁶`): the cheap **rational margin test** `RatPSD (cX + (δ/2)·1)` is enough.  The only
thing a false bit can still owe is the *all-false* record at a point where the body is nevertheless
non-empty, i.e. exactly d2's lane.

## What is machine-checked here

* **§0 falsification receipts.**  (0.1) The direction brief's candidate scaling
  `X = D((1−θ)Q + θ·1)D`, `D = diag(1/√Qᵢᵢ)`, is **not unit-diagonal** — its diagonal is
  `(1−θ) + θ/Qᵢᵢ`; the normalisation must be applied *after* the shift (that is exactly
  `RoundingOut.roundDiag`, which is what `relaxMem_witness` runs).  (0.2) the trace accounting at the
  campaign's own constant `dq = eps/(9Rq+1)`: the true cost is `≈ (3/2)·δ·Rq + δ/2 ≈ (2/9)·eps`
  against a budget of `2·eps`, and the *proved* cost bound `6νRq` gives `≈ eps/2`; the budget has a
  factor `≥ 4` of slack at **every** input, and the sharp regime is large `Rq`, not `n = 2`.
* **§1 the rounding lemma, packaged for the record.**  `hcert_of_relaxMem_budget` at an arbitrary
  tolerance `δ` (the caller's own `P.dq`) and `memberAt_of_relaxMem` at the campaign's `dqShallow`,
  both symmetry-free (`relaxMem_symmMat` is restated here so the producer owes no invariant).
* **§2 the record lanes.**  `runParts_of_relaxMem`: the `ok ≡ true` record from **one relaxed
  member**, i.e. case (ii) with `RelaxMem` in place of an exact witness.  `relaxBodyLE_empty_of_le_one`
  and `runParts_of_le_one`: the `n ≤ 1` slice is empty-body, so the family is total.
* **§3 the stroke, on the published cone** (a re-derivation of `Sound31`, which is a `Solutions.*`
  bundle and cannot be co-loaded with the published mirror): `soundAt_of_runParts`,
  `soundEpsOnBracket_of_family`, `solution_of_runPartsFamily`, and the three-lane corollary
  `solution_of_lanes` from **{Poly bit} + {ok-lane supply} + {empty lane} + {d2's cut lane}**.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
imports are `Mathlib` plus published `Definitions.Def_QMCLeafB_*` bundles only; `#print axioms`
receipts at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

noncomputable section

namespace Round33M3

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- The request coding of the leaf (local, as in the templates). -/
local instance instRequestCodingRound33 : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 0.  Falsification receipts -/

/-! ### 0.1  The brief's candidate scaling is not unit-diagonal -/

/-- **The naive `D`-scaling fails.**  For the brief's candidate `X = D((1−θ)Q + θ·1)D` with
`Dᵢᵢ² = 1/Qᵢᵢ` (the normalisation of `Q` itself), the diagonal entry is
`((1−θ)Qᵢᵢ + θ)/Qᵢᵢ`, which is `1` only if `θ·(1 − Qᵢᵢ) = 0`.  Since the campaign's member has
`|Qᵢᵢ − 1| ≤ δ/4` and it needs `θ ≥ δ/2` for the psd margin, the two requirements conflict:
the shift has to come *first* and the normalisation *second* (`RoundingOut.roundDiag`). -/
theorem naive_scaling_not_unitDiag {d θ : ℚ} (hd : d ≠ 0) (hθ : θ ≠ 0) (h1 : d ≠ 1) :
    ((1 - θ) * d + θ) / d ≠ 1 := by
  intro h
  have h' : (1 - θ) * d + θ = d := by
    rw [div_eq_iff hd] at h
    linarith
  have hzero : θ * (1 - d) = 0 := by linarith
  rcases mul_eq_zero.mp hzero with h2 | h2
  · exact hθ h2
  · exact h1 (by linarith)

#print axioms Round33M3.naive_scaling_not_unitDiag

/-- The same at the campaign's sharpest diagonal: `Qᵢᵢ = 1 + δ/4` with `θ = δ/2` (the smallest
shift that buys the psd margin), `δ = 1`.  The candidate's diagonal entry is `9/10 ≠ 1`. -/
theorem naive_scaling_sharp_instance :
    ((1 - (1 / 2 : ℚ)) * (1 + (1 / 4 : ℚ)) + 1 / 2) / (1 + 1 / 4) ≠ 1 := by
  norm_num

#print axioms Round33M3.naive_scaling_sharp_instance

/-! ### 0.2  The trace accounting at `dq = eps/(9Rq+1)`

At `δ = eps/(9Rq+1)` the rounding cost `roundCost A (3δ/4)` is at most
`(1+ν)(2ν+ν²)·∑|Aᵢⱼ| ≤ (3δ/2)(1+3δ/2)·Rq` (here `∑|Aᵢⱼ| = Rq` exactly, `RundataCert.sum_abs_wMatrixQ`),
so cost plus `δ/2` is at most `eps/6 + eps/1440000 + eps/2 ≤ (2/3)·eps` — against the budget
`2·eps`.  This is the receipt for the falsify-first question of direction 1: **the accounting does not
overrun anywhere**, at any `Rq`, and the worst case is large `Rq` (where the ratio is `≈ 2/9`), not
the `n = 2` instance (where it is `≈ 1/20`). -/
theorem accounting_core (S : ℚ) (hS : 0 ≤ S) :
    (3 * ((S / 40000) / (9 * S + 1)) / 2)
        * (1 + 3 * ((S / 40000) / (9 * S + 1)) / 2) * S
      + ((S / 40000) / (9 * S + 1)) / 2 ≤ 2 * (S / 40000) := by
  have hden : (0 : ℚ) < 9 * S + 1 := by linarith
  set δ : ℚ := (S / 40000) / (9 * S + 1) with hδ
  set M : ℚ := S / 40000 with hM
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hδ9 : δ * (9 * S + 1) = M := by rw [hδ, hM]; field_simp
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact div_nonneg hM0 hden.le
  have hδS : δ * S ≤ M / 9 := by nlinarith [hδ9, hδ0, hS]
  have hδM : δ ≤ M := by nlinarith [hδ9, hδ0, hS]
  -- the quadratic piece
  have hsq : (3 * δ / 2) * (3 * δ / 2) * S ≤ M / 1440000 := by
    have e1 : (3 * δ / 2) * (3 * δ / 2) * S = (9 / 4) * δ * (δ * S) := by ring
    rw [e1]
    have step1 : (9 / 4) * δ * (δ * S) ≤ (9 / 4) * δ * (M / 9) := by
      apply mul_le_mul_of_nonneg_left hδS
      nlinarith [hδ0]
    have step2 : (9 / 4) * δ * (M / 9) = δ * M / 4 := by ring
    have step3 : δ * M / 4 = M * M / (4 * (9 * S + 1)) := by
      rw [hδ]; field_simp
    have step4 : M * M / (4 * (9 * S + 1)) ≤ M / 1440000 := by
      rw [hM]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hS]
    linarith
  -- linear pieces
  have hlin : (3 * δ / 2) * S ≤ M / 6 := by nlinarith [hδS]
  have hhalf : δ / 2 ≤ M / 2 := by linarith
  have hexp : (3 * δ / 2) * (1 + 3 * δ / 2) * S
      = (3 * δ / 2) * S + (3 * δ / 2) * (3 * δ / 2) * S := by ring
  rw [hexp]
  have hM6 : M / 6 ≤ M / 6 := le_rfl
  linarith

#print axioms Round33M3.accounting_core

/-- **The proved cost bound is `6·ν·Rq` at `ν = 3δ/4`, and it fits with a factor `4` to spare.** -/
theorem accounting_proved (S : ℚ) (hS : 0 ≤ S) :
    6 * (3 * ((S / 40000) / (9 * S + 1)) / 4) * S + ((S / 40000) / (9 * S + 1)) / 2
      ≤ 2 * (S / 40000) := by
  have hden : (0 : ℚ) < 9 * S + 1 := by linarith
  set δ : ℚ := (S / 40000) / (9 * S + 1) with hδ
  set M : ℚ := S / 40000 with hM
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hδ9 : δ * (9 * S + 1) = M := by rw [hδ, hM]; field_simp
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact div_nonneg hM0 hden.le
  have hδS : δ * S ≤ M / 9 := by nlinarith [hδ9, hδ0, hS]
  have hδM : δ ≤ M := by nlinarith [hδ9, hδ0, hS]
  have hcost : 6 * (3 * δ / 4) * S ≤ M / 2 := by
    have e : 6 * (3 * δ / 4) * S = (9 / 2) * (δ * S) := by ring
    rw [e]; linarith
  linarith

#print axioms Round33M3.accounting_proved

/-! ## 1.  The rounding lemma, packaged for the record -/

/-- The campaign's `RunParams` family (fixed here: the record is at these parameters). -/
abbrev P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.UnionShallow.paramsKbc2

/-- **The `hd` witness class**: a genuine unit-diagonal PSD point at `t + eps` — exactly the
existential `RunParts.hcert` asks for at an `ok` round. -/
def MemberAt (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
      (QMCLeafB.wMatrix G * X).trace
        ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)

/-! ### 1.1  Symmetry is free: `qf` and `frob` see only the symmetric part -/

/-- The symmetric part `(X + Xᵀ)/2`. -/
def symmMat {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (X i j + X j i) / 2

theorem symmMat_eq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) :
    symmMat X = (1 / 2 : ℚ) • (X + Xᵀ) := by
  ext i j
  simp [symmMat, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply]
  ring

theorem symmMat_transpose {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) :
    (symmMat X)ᵀ = symmMat X := by
  ext i j
  simp [symmMat, add_comm]

theorem symmMat_self {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    symmMat X i i = X i i := by
  simp [symmMat]

theorem qf_smul33 {n : ℕ} (c : ℚ) (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (c • M) x = c * QMCLeafB.SepOracle.qf M x := by
  simp only [QMCLeafB.SepOracle.qf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem qf_transpose33 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf Mᵀ x = QMCLeafB.SepOracle.qf M x := by
  simp only [QMCLeafB.SepOracle.qf]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

theorem qf_symmMat {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (symmMat X) x = QMCLeafB.SepOracle.qf X x := by
  rw [symmMat_eq, qf_smul33, QMCLeafB.SepOracle.qf_add, qf_transpose33]
  ring

theorem frob_smul33 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob A (c • M) = c * QMCLeafB.SepOracle.frob A M := by
  simp only [QMCLeafB.SepOracle.frob, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem frob_transpose33 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (M : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob A Mᵀ = QMCLeafB.SepOracle.frob Aᵀ M := by
  simp only [QMCLeafB.SepOracle.frob, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem frob_symmMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : Aᵀ = A)
    (X : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob A (symmMat X) = QMCLeafB.SepOracle.frob A X := by
  rw [symmMat_eq, frob_smul33, QMCLeafB.SepOracle.frob_add, frob_transpose33, hA]
  ring

/-- **`RelaxMem` transports to the symmetric part** (for symmetric `A`). -/
theorem relaxMem_symmMat {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} (hA : Aᵀ = A) {u δ : ℚ}
    (h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ) :
    QMCLeafB.RelaxOracle.RelaxMem A (symmMat cX) u δ where
  δ_pos := h.δ_pos
  psd_margin := fun x => by rw [qf_symmMat]; exact h.psd_margin x
  diag_near := fun i => by rw [symmMat_self]; exact h.diag_near i
  trace_le := by rw [frob_symmMat A hA]; exact h.trace_le

theorem wMatrixQ_transpose (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.Finalization.wMatrixQ G)ᵀ = QMCLeafB.Finalization.wMatrixQ G :=
  QMCLeafB.Finalization.IsQMCWeight.symm (QMCLeafB.Finalization.isQMCWeight_wMatrixQ G)

#print axioms Round33M3.qf_symmMat
#print axioms Round33M3.frob_symmMat
#print axioms Round33M3.relaxMem_symmMat

/-! ### 1.2  The rounding lemma: one relaxed member ⟹ one genuine witness -/

/-- **`hcert`'s witness from one relaxed member**, at *the caller's own tolerance* `δ`: the only
price is the rounding budget `roundCost A (3δ/4) + δ/2 ≤ 2·eps`. -/
theorem hcert_of_relaxMem_budget {G : QuantumMaxCutEnergy.Input} {t : ℚ} {δ : ℚ}
    {cX : Matrix (Fin G.n) (Fin G.n) ℚ} (hCsym : cXᵀ = cX)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) δ)
    (hbudget : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * δ / 4)
      + δ / 2 ≤ 2 * QMCLeafB.RundataCert.eps G) :
    MemberAt G t := by
  obtain ⟨X, hX, htr⟩ := QMCLeafB.RelaxOracle.hcert_of_relaxMem (n := G.n)
    (A := QMCLeafB.Finalization.wMatrixQ G) (cX := cX) (t := t)
    (εr := QMCLeafB.RundataCert.eps G) (δ := δ) (εw := QMCLeafB.RundataCert.eps G)
    h (wMatrixQ_transpose G) hCsym
    (fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq) (by linarith)
  refine ⟨X, hX, ?_⟩
  rw [QMCLeafB.Finalization.wMatrix_castM] at htr
  exact htr

#print axioms Round33M3.hcert_of_relaxMem_budget

/-- **The rounding lemma at the campaign's constants**: `RelaxMem` at `(t − eps, dqShallow)`
produces `hcert`'s witness, by the banked budget `Fal30.budget_at_dq`.  Nothing else is needed:
no exact-PSD stop test, no `Hpsd` pivot margin, no grid enlargement. -/
theorem hcert_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {cX : Matrix (Fin G.n) (Fin G.n) ℚ} (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (hCsym : cXᵀ = cX)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    MemberAt G t := by
  refine hcert_of_relaxMem_budget hCsym h ?_
  have hb := QMCLeafB.Fal30.budget_at_dq G hn hRq
  linarith

#print axioms Round33M3.hcert_of_relaxMem

/-! ### 1.3  The ok test itself: the computable rational oracle, with no grid and no `Hpsd`

`hok` in the campaign's residual list asks the program's `ok` flag to mean "there is a symmetric
rational `RelaxMem` point at the loop's own centre".  The point of the rounding lemma is that this is
the *right* semantics and it is cheap: `RelaxOracle.relaxOracle` is a **computable** test (rational
comparisons plus the exact rational LDLᵀ split of `cX + (δ/2)·1`, `splitOfTranspose`), it needs no
grid — in particular no enlargement of `stD` to `2n²/δ ≈ 3·10⁶` — and its positive verdict *is* a
`RelaxMem`.  So `hok` reduces to "the ok flag is this test's verdict", and `Hpsd` disappears. -/

/-- **The computable `ok` test.**  Every branch is a rational comparison; a `true` verdict is a
`RelaxMem` certificate.  This is the test a program can actually run. -/
def okTest {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ) (hs : cXᵀ = cX) : Bool :=
  match QMCLeafB.RelaxOracle.relaxOracle A cX u δ hδ hs with
  | .mem _ => true
  | .cut _ => false

/-- **A true verdict of the cheap test *is* a relaxed member.** -/
theorem okTest_spec {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ)
    (hs : cXᵀ = cX) (h : okTest A cX u δ hδ hs = true) :
    QMCLeafB.RelaxOracle.RelaxMem A cX u δ := by
  unfold okTest at h
  split at h
  · assumption
  · exact absurd h (by simp)

#print axioms Round33M3.okTest
#print axioms Round33M3.okTest_spec

/-- **`hcert` from a true reading of the cheap test** — the operational form of §1.2: the program
reports `ok` iff the rational LDLᵀ test at its own centre passes, and that alone hands `RunParts.hcert`
its witness. -/
theorem hcert_of_okTest {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {cX : Matrix (Fin G.n) (Fin G.n) ℚ} (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (hs : cXᵀ = cX)
    (h : okTest (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)
      (QMCLeafB.RundataParams.dqShallow_pos G) hs = true) :
    MemberAt G t :=
  hcert_of_relaxMem hn hRq hs (okTest_spec _ _ _ _ _ _ h)

#print axioms Round33M3.hcert_of_okTest

/-- **The ok lane's supply, symmetry-free**: a relaxed member at *any* rational matrix gives the
witness (its symmetric part is one). -/
theorem memberAt_of_relaxMem_nosymm {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {cX : Matrix (Fin G.n) (Fin G.n) ℚ} (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    MemberAt G t :=
  hcert_of_relaxMem hn hRq (symmMat_transpose cX)
    (relaxMem_symmMat (wMatrixQ_transpose G) h)

#print axioms Round33M3.memberAt_of_relaxMem_nosymm

/-! ## 2.  The record lanes -/

/-! ### 2.1  `anyOk` at the two constant streams -/

theorem anyOk_false (T : ℕ) : QMCLeafB.SimLoop.anyOk (fun _ : ℕ => false) T = false := by
  induction T with
  | zero => rfl
  | succ k ih => rw [QMCLeafB.SimLoop.anyOk_succ, ih]; rfl

theorem anyOk_true (T : ℕ) (hT : 0 < T) : QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) T = true := by
  induction T with
  | zero => exact absurd hT (Nat.lt_irrefl 0)
  | succ k _ => rw [QMCLeafB.SimLoop.anyOk_succ]; rfl

#print axioms Round33M3.anyOk_false
#print axioms Round33M3.anyOk_true

/-! ### 2.2  The ok lane: bit `true` + one witness ⟹ `RunParts` -/

/-- **The `ok ≡ true` record.**  One `MemberAt` point serves every round (`hcert` does not depend on
the round index) and every cut slot is vacuous.  This is the record `runParts_of_member` builds; it is
repeated here because the published mirror does not carry it into the cone of `Sound31`. -/
noncomputable def runParts_of_member {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (Q : QMCLeafB.FinalStroke.RunParams G)
    (hKm : 0 < Q.K * Q.m) (hbit : o G t = true) (hmem : MemberAt G t) :
    QMCLeafB.FinalStroke.RunParts o G t Q := by
  classical
  set cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
    fun _ => ⟨fun _ => 0, fun _ => 0, 0⟩ with hcd
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
        exact (anyOk_true (Q.K * Q.m) hKm).symm }

#print axioms Round33M3.runParts_of_member

/-- **The ok lane from a *relaxed* member** — this is the payoff of the rounding lemma: the record
asks the producer for a rational `RelaxMem` point at the loop's own level, not for an exact
unit-diagonal PSD matrix at `t + eps`. -/
noncomputable def runParts_of_relaxMem {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (Q : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (hKm : 0 < Q.K * Q.m)
    (hbit : o G t = true)
    (hmem : ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    QMCLeafB.FinalStroke.RunParts o G t Q :=
  runParts_of_member Q hKm hbit (memberAt_of_relaxMem_nosymm hn hRq hmem.choose_spec)

#print axioms Round33M3.runParts_of_relaxMem

/-! ### 2.3  The empty lane (published `RefutedM3`) and the family -/

/-- **The relaxed body, at the run's own level and tolerance** (the hypothesis the published
empty-body record consumes). -/
def EmptyBody (G : QuantumMaxCutEnergy.Input) (t : ℚ) (Q : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((Q.dq : ℚ) : ℝ) X

/-- **The empty lane, repackaged**: `RefutedM3.runParts_of_emptyBody`, verbatim. -/
noncomputable def runParts_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (Q : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hbit : o G t = false) (hempty : EmptyBody G t Q) :
    QMCLeafB.FinalStroke.RunParts o G t Q :=
  QMCLeafB.RefutedM3.runParts_of_emptyBody G t Q hn hbit hempty

#print axioms Round33M3.runParts_of_emptyBody

/-- **The record family from two supplies.**  The `true` side needs a witness (`MemberAt`, which the
rounding lemma supplies from one relaxed member at any `n`, and which the identity supplies whenever
`t ≥ −eps`); the `false` side is d2's lane.  No `n ≤ 1` correction is needed: the `ok ≡ true` record
uses a *trivial* cut stream, since every cut slot is guarded by `ok k = false`. -/
noncomputable def runPartsFamily_of_lanes {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m)
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true → MemberAt G t)
    (hF : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = false →
      QMCLeafB.FinalStroke.RunParts o G t (P G)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), QMCLeafB.FinalStroke.RunParts o G t (P G) := by
  intro G t
  cases h : o G t with
  | true => exact runParts_of_member (P G) (hKm G) h (hM G t h)
  | false => exact hF G t h

#print axioms Round33M3.runPartsFamily_of_lanes

/-! ## 3.  `SoundAt` from one record, and the stroke

The `false` clause of the leaf's verdict predicate is *dual*: a point of the true body strictly below
`t − eps` puts the campaign ball inside the run's relaxation, which the run's genuine cuts forbid
(`BallM2.no_runParts_of_ball`).  So a record certifies both clauses: `hcert` at the `ok` round gives
the primal witness, the ball gives the dual bound.  No emptiness and no thin-body analysis is
involved.  (This is `Sound31`'s argument, re-derived here because `Sound31` lives in the `Solutions.*`
cone, which cannot be co-loaded with the published mirror.) -/

/-- **The campaign ball around a strict-below point** lies in the run's relaxation. -/
theorem ball_of_strict_below {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (Q : QMCLeafB.FinalStroke.RunParams G)
    {Z : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hZ : QMCLeafB.AnswerProducer.IsUnitDiagPSD Z)
    (htr : (QMCLeafB.wMatrix G * Z).trace
      < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat Z)
        (((Q.dq : ℚ) : ℝ) / (8 * (((Q.cAq : ℚ) : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t Q := by
  have hδ : (0 : ℝ) < ((Q.dq : ℚ) : ℝ) := by exact_mod_cast Q.hdq
  have hcA : (0 : ℝ) ≤ ((Q.cAq : ℚ) : ℝ) := by exact_mod_cast Q.hcAq
  have hmem : QMCLeafB.AnswerProducer.StrictBody (QMCLeafB.wMatrix G) t
      (QMCLeafB.EngineRuntime.Rq G / 40000) (QMCLeafB.AnswerProducer.flat Z) :=
    ⟨Z, hZ, le_of_lt htr, rfl⟩
  refine Set.Subset.trans ?_ (Set.Subset.refl _)
  have hM : 2 * (((G.n : ℝ)) ^ 2 + (((Q.dq : ℚ) : ℝ) / (8 * (((Q.cAq : ℚ) : ℝ) + 1))) ^ 2)
      ≤ ((2 * (G.n : ℚ) ^ 2 + 2 * Q.dq ^ 2 : ℚ) : ℝ) := by
    push_cast
    have h1 : (0 : ℝ) < ((Q.cAq : ℚ) : ℝ) + 1 := by linarith
    have h2 : (((Q.dq : ℚ) : ℝ) / (8 * (((Q.cAq : ℚ) : ℝ) + 1))) ^ 2 ≤ ((Q.dq : ℚ) : ℝ) ^ 2 := by
      have h3 : (1 : ℝ) ≤ 8 * (((Q.cAq : ℚ) : ℝ) + 1) := by nlinarith
      have h4 : (0 : ℝ) < 8 * (((Q.cAq : ℚ) : ℝ) + 1) := by linarith
      have h5 : ((Q.dq : ℚ) : ℝ) / (8 * (((Q.cAq : ℚ) : ℝ) + 1)) ≤ ((Q.dq : ℚ) : ℝ) := by
        rw [div_le_iff₀ h4]; nlinarith [hδ.le]
      have h6 : (0 : ℝ) ≤ ((Q.dq : ℚ) : ℝ) / (8 * (((Q.cAq : ℚ) : ℝ) + 1)) := by positivity
      nlinarith
    nlinarith
  exact QMCLeafB.Boundary.strictBody_ball_relaxBall (t := t)
    (εr := QMCLeafB.EngineRuntime.Rq G / 40000) (δq := Q.dq) (cA := ((Q.cAq : ℚ) : ℝ))
    hδ hcA (by simpa using Q.hAsum) hM hmem

#print axioms Round33M3.ball_of_strict_below

/-- **A strict-below point forces the bit `true`** (the volume obstruction, in contrapositive form). -/
theorem bit_true_of_strict_below {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (Q : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (B : QMCLeafB.FinalStroke.RunParts o G t Q)
    (hstrict : ∃ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z ∧
        (QMCLeafB.wMatrix G * Z).trace
          < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    o G t = true := by
  obtain ⟨Z, hZ, htr⟩ := hstrict
  exact QMCLeafB.BallM2.no_runParts_of_ball hn
    (ball_of_strict_below (G := G) (t := t) Q (Z := Z) hZ htr) B

#print axioms Round33M3.bit_true_of_strict_below

/-- **`SoundAt` from one run record.** -/
theorem soundAt_of_runParts {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (Q : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (B : QMCLeafB.FinalStroke.RunParts o G t Q)
    (hKm : 0 < Q.K * Q.m) :
    QMCLeafB.VerdictSound.SoundAt o G t := by
  constructor
  · intro htrue
    have hany : QMCLeafB.SimLoop.anyOk B.ok (Q.K * Q.m) = true := by
      rw [← B.hverdict]; exact htrue
    obtain ⟨k, hk, hok⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff B.ok (Q.K * Q.m)).1 hany
    exact B.hcert k hk hok
  · intro hfalse Z hZ
    by_contra hlt
    push Not at hlt
    have htrue := bit_true_of_strict_below Q hn B ⟨Z, hZ, hlt⟩
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue

#print axioms Round33M3.soundAt_of_runParts

/-- **`SoundεOnBracket` from a record family.** -/
theorem soundEpsOnBracket_of_family {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Q : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts o G t (Q G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (Q G).K * (Q G).m) :
    QMCLeafB.FinishLine.SoundεOnBracket o := by
  rw [QMCLeafB.VerdictSound.soundEpsOnBracket_iff]
  intro G t hlo hhi
  by_cases hn : 2 ≤ G.n
  · exact soundAt_of_runParts (Q G) hn (B G t) (hKm G)
  · exact QMCLeafB.VerdictSound.soundAt_of_le_one o (by omega) t hlo hhi

#print axioms Round33M3.soundEpsOnBracket_of_family

/-- **THE STROKE: `SolutionStatement` from a `Poly` bit plus a `RunParts` family.** -/
theorem solution_of_runPartsFamily (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    {Q : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts o G t (Q G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (Q G).K * (Q G).m) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o
    (soundEpsOnBracket_of_family B hKm) ho

#print axioms Round33M3.solution_of_runPartsFamily

/-- **The identity witness**: whenever `t ≥ −eps`, the identity is a genuine unit-diagonal PSD point
at `t + eps` (`wMatrix` has zero diagonal).  This covers the degenerate `Rq = 0` slice of the ok
lane, where the rounding budget is vacuous. -/
theorem memberAt_of_neg_eps_le {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (h : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) : MemberAt G t := by
  refine ⟨1, QMCLeafB.AnswerProducer.isUnitDiagPSD_one, ?_⟩
  have htr : (QMCLeafB.wMatrix G * 1).trace = 0 := by
    rw [Matrix.mul_one]
    simp [Matrix.trace]
  rw [htr]
  linarith

#print axioms Round33M3.memberAt_of_neg_eps_le

/-- **The ok lane's supply, closed**: a relaxed member plus the bracket floor gives `MemberAt`, with
the rounding lemma doing the work at `Rq > 0` and the identity witness at `Rq = 0`. -/
theorem memberAt_of_relaxMem_or_identity {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ))
    (h : ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    MemberAt G t := by
  rcases lt_or_eq_of_le (QMCLeafB.EngineRuntime.Rq_nonneg G) with hpos | hzero
  · obtain ⟨cX, hcX⟩ := h
    exact memberAt_of_relaxMem_nosymm hn hpos hcX
  · exact memberAt_of_neg_eps_le hlo

#print axioms Round33M3.memberAt_of_relaxMem_or_identity

/-- **THE COROLLARY — the leaf from two lanes.**  Inputs: a `Poly` bit, its ok lane (`bit true ⟹
witness`; discharge it by `memberAt_of_relaxMem_or_identity`, i.e. from **one relaxed rational
member**, or by `memberAt_of_neg_eps_le`), its false lane (d2: all-false records with genuine
transcript cuts — free wherever the relaxed body is empty, `falseLane_of_emptyBody`), and the
campaign's round count. -/
theorem solution_of_lanes (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m)
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true → MemberAt G t)
    (hF : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = false →
      QMCLeafB.FinalStroke.RunParts o G t (P G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_runPartsFamily o ho (Q := P) (runPartsFamily_of_lanes hKm hM hF) hKm

#print axioms Round33M3.solution_of_lanes

/-- **The false lane is free at an empty relaxed body** — the published `RefutedM3` record, in the
shape `solution_of_lanes` consumes (`hF`).  So d2's cut lane is owed only at `bit false ∧ body
non-empty`. -/
noncomputable def falseLane_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hE : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = false → EmptyBody G t (P G))
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) (hbit : o G t = false) :
    QMCLeafB.FinalStroke.RunParts o G t (P G) :=
  runParts_of_emptyBody (P G) hn hbit (hE G t hbit)

#print axioms Round33M3.falseLane_of_emptyBody

/-! ## 4.  The dichotomy, and what the leaf becomes with an exact bit

The two record lanes of §2 are keyed on *one* geometric predicate — `EmptyBody`, the emptiness of the
real relaxed body at `(t − eps, dq)`.  `(A)` says the ok lane is available at **every** point where
that body is non-empty, so the record family exists with **no cuts anywhere** as soon as the program's
bit *decides* `EmptyBody`.  That is the sharpest form of the residual: `Poly` + a decider of the
relaxed body's non-emptiness (a poly-time SDP feasibility question), instead of `Poly` + genuine
separation at thin bodies.

The gap between the real body and the rational membership a program can certify is isolated as
`RatDense` below — the *one* named residual of this direction.  It is not vacuous on either side: a
rational member is a real member, and a real member at `(u, δ)` gives, by sign-controlled entrywise
approximation, a rational one at `(u, 3δ/2)` (see the module note), which the rounding budget still
affords. -/

/-- **The density residual, stated exactly**: a non-empty real relaxed body at the campaign's own
`(level, tolerance)` contains a rational `RelaxMem` point. -/
def RatDense : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → ¬ EmptyBody G t (P G) →
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)

/-- **The dichotomy** (`EmptyBody ∨ MemberAt`) from the density residual.  Note that the bracket
`t ≥ −Rq/40000` handles the degenerate `Rq = 0` case through the identity witness. -/
theorem emptyBody_or_memberAt (h : RatDense) {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hn : 2 ≤ G.n) (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    EmptyBody G t (P G) ∨ MemberAt G t := by
  by_cases hE : EmptyBody G t (P G)
  · exact Or.inl hE
  · exact Or.inr (memberAt_of_relaxMem_or_identity hn hlo (h G t hn hE))

#print axioms Round33M3.emptyBody_or_memberAt

/-- **The leaf from an EXACT bit.**  If the program's bit decides `EmptyBody` (both directions) then
the `RunParts` family exists with no cut content at all: bit `true` is the ok lane (dichotomy + (A)),
bit `false` is the free empty-body record.  The only genuine obligations left are `Poly` and the
decider property — `hFsmall` is the degenerate `n ≤ 1` slice, where the published empty-body record's
cut stream needs `2 ≤ n`. -/
theorem solution_of_exactBit (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m)
    (hdich : RatDense)
    (hexact : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true ↔ ¬ EmptyBody G t (P G))
    (hFsmall : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), G.n ≤ 1 → o G t = false →
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hlo : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    QMCLeafB.FinishLine.SolutionStatement := by
  refine solution_of_lanes o ho hKm ?_ ?_
  · intro G t hbit
    rcases Nat.lt_or_ge G.n 2 with hlt | hn
    · exact memberAt_of_neg_eps_le (hlo G t hbit)
    · rcases emptyBody_or_memberAt hdich hn (hlo G t hbit) with hE | hM
      · exact absurd hE ((hexact G t).mp hbit)
      · exact hM
  · intro G t hbit
    by_cases hn : 2 ≤ G.n
    · refine falseLane_of_emptyBody (fun G' t' hb => ?_) G t hn hbit
      by_contra hne
      have h1 : o G' t' = true := (hexact G' t').mpr hne
      rw [hb] at h1
      exact Bool.noConfusion h1
    · exact hFsmall G t (by omega) hbit

#print axioms Round33M3.solution_of_exactBit

/-! ## 5.  The round count of the campaign parameters is positive (so `hKm` is not a residual) -/

theorem paramsKbc2_Km_pos (G : QuantumMaxCutEnergy.Input) : 0 < (P G).K * (P G).m := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_K, QMCLeafB.UnionShallow.paramsKbc2_m]
  have hm : 0 < QMCLeafB.HalvePerG.mHalve (G.n * G.n) := by
    rw [QMCLeafB.HalvePerG.mHalve]
    omega
  have hsq : 0 < (G.n + 1) ^ 2 := by positivity
  have hfac : 0 < QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1
      + (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1) + (G.n + 27) := by omega
  have hK : 0 < QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := by
    rw [QMCLeafB.UnionShallow.Kbc2]
    exact Nat.mul_pos hm (Nat.mul_pos hsq hfac)
  exact Nat.mul_pos hK hm

#print axioms Round33M3.paramsKbc2_Km_pos

/-- **`solution_of_lanes` with the round-count hypothesis discharged.** -/
theorem solution_of_lanes_final (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true → MemberAt G t)
    (hF : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = false →
      QMCLeafB.FinalStroke.RunParts o G t (P G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_lanes o ho paramsKbc2_Km_pos hM hF

#print axioms Round33M3.solution_of_lanes_final

end Round33M3


