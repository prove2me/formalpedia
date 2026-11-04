-- Prove2me | Definitions.Def_QMCLeafB_residRefute
-- name    : QMCLeafB_residRefute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:42:28.735796+00:00
-- url     : https://prove2.me/theorems/a242f807-b2db-43e5-ae25-0d668e439a1d
-- title:
--   QMCLeafB residRefute
-- statement:
--   # leaf B — `resid-refute` (member m8): the all-`false` flag stream is impossible
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_sim_loop_m6
import Definitions.Def_QMCLeafB_final_stroke_m7
/-
# leaf B — `resid-refute` (member m8): the all-`false` flag stream is impossible

Phase 18's endgame (`QMCLeafB.ClosingAssembly.Resid`) asks, for every interior `(G, t)`, for a
`Bundle` whose flag stream satisfies

    hokAll : ∀ k, k < P.K * P.m → ok k = false        -- "every round of the loop is a cut round"

together with `hverdict : o G t = anyOk ok (P.K * P.m)`.  This file **refutes that slot**.

At the two-vertex graph with every edge of weight `1/2` (`Rq = 1`) and `t = -1/2`, the refuted
branch's own soundness theorem (`SimLoop.simulate_refuted_sound`) applied to an all-cut bundle
concludes

    ∀ Z, IsUnitDiagPSD Z → (t : ℝ) - Rq/40000 ≤ (wMatrix G * Z).trace,

which is **false** at `Z = !![1, -1; -1, 1]`: `(wMatrix G * Z).trace = -1 < -1/2 - 1/40000`.  So no
`RunParts` bundle at `(G₀, -1/2)` can have an all-`false` flag stream.

The statement is made about the shelf's `RunParts` rather than about phase 18's `Bundle`, so it does
not depend on phase 18's file: any route that derives the refuted branch from an all-`false` stream
— which is what `Bundle.hokAll` + `Bundle.hverdict` do — runs into this.  The flag stream of the
campaign's engine is *not* all-`false` at feasible thresholds: on the interior bracket the run must
be split into the all-cut case (refutation) and the ok case (witness), which is exactly the split
`RunParts`/`RunData` carries.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.ResidRefute

open QuantumMaxCutEnergy

local instance instRequestCodingRefute :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The two-vertex graph with all edge weights `1/2` -/

/-- **`G₀`**: two vertices, the single edge of weight `1/2`, so `Rq G₀ = 1`.  (`abbrev`, so that
`Fin G₀.n` is reducibly `Fin 2` and the concrete matrix algebra below goes through.) -/
abbrev G₀ : QuantumMaxCutEnergy.Input :=
  ⟨2, fun _ => (1 / 2 : ℚ≥0)⟩

/-- The edge set of two vertices is a singleton. -/
theorem univ_edge_two : (Finset.univ : Finset (Edge 2))
    = {⟨(0, 1), by decide⟩} := by
  ext e
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  obtain ⟨⟨i, j⟩, h⟩ := e
  have hij : (i : ℕ) < (j : ℕ) := h
  have hi : (i : ℕ) < 2 := i.isLt
  have hj : (j : ℕ) < 2 := j.isLt
  refine Subtype.ext ?_
  show ((i, j) : Fin 2 × Fin 2) = ((0 : Fin 2), (1 : Fin 2))
  rw [Prod.mk.injEq]
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- **`Rq G₀ = 1`.** -/
theorem Rq_G₀ : QMCLeafB.EngineRuntime.Rq G₀ = 1 := by
  unfold QMCLeafB.EngineRuntime.Rq
  show 2 * (∑ e : Edge G₀.n, ((G₀.weights e : ℚ≥0) : ℚ)) = 1
  rw [univ_edge_two, Finset.sum_singleton]
  norm_num

/-! ## 2.  The witness `!![1, -1; -1, 1]` -/

/-- The witness: unit diagonal, positive semidefinite, and `(wMatrix G₀ * Z).trace = -1`. -/
noncomputable def Z₀ : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

theorem Z₀_isUnitDiagPSD : QMCLeafB.AnswerProducer.IsUnitDiagPSD Z₀ := by
  refine ⟨?_, fun i => ?_⟩
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Z₀]
    · intro x
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Z₀,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.of_apply, Matrix.empty_val', star_trivial]
      nlinarith [sq_nonneg (x 0 - x 1)]
  · fin_cases i <;> simp [Z₀]

/-- **`tr (wMatrix G₀ · Z₀) = -1`.** -/
theorem trace_G₀_Z₀ : (QMCLeafB.wMatrix G₀ * Z₀).trace = -1 := by
  have e00 : QMCLeafB.wMatrix G₀ (0 : Fin G₀.n) (0 : Fin G₀.n) = 0 :=
    QMCLeafB.wMatrix_apply_of_eq
  have e11 : QMCLeafB.wMatrix G₀ (1 : Fin G₀.n) (1 : Fin G₀.n) = 0 :=
    QMCLeafB.wMatrix_apply_of_eq
  have e01 : QMCLeafB.wMatrix G₀ (0 : Fin G₀.n) (1 : Fin G₀.n) = 1 / 2 := by
    unfold QMCLeafB.wMatrix
    norm_num [G₀]
  have e10 : QMCLeafB.wMatrix G₀ (1 : Fin G₀.n) (0 : Fin G₀.n) = 1 / 2 := by
    unfold QMCLeafB.wMatrix
    norm_num [G₀]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply, e00, e01, e10, e11,
    Z₀, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    star_trivial]
  norm_num

/-! ## 3.  `anyOk` of an all-`false` stream -/

theorem anyOk_all_false (ok : ℕ → Bool) :
    ∀ N : ℕ, (∀ k, k < N → ok k = false) → QMCLeafB.SimLoop.anyOk ok N = false
  | 0, _ => rfl
  | (k + 1), h => by
      rw [QMCLeafB.SimLoop.anyOk_succ, h k (Nat.lt_succ_self k),
        anyOk_all_false ok k (fun j hj => h j (Nat.lt_succ_of_lt hj))]
      rfl

/-! ## 4.  No all-`false` `RunParts` bundle at `(G₀, -1/2)` -/

/-- **The refutation.**  A `RunParts` bundle at `(G₀, -1/2)` whose flag stream is all-`false` cannot
exist: its own refuted-branch soundness contradicts the explicit witness `Z₀`. -/
theorem no_runParts_allFalse
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : QMCLeafB.FinalStroke.RunParams G₀)
    (R : QMCLeafB.FinalStroke.RunParts o G₀ (-(1 / 2)) P)
    (hok : ∀ k, k < P.K * P.m → R.ok k = false) : False := by
  set Rd := R.toRunData with hRd
  have hKm : Rd.K * Rd.m = P.K * P.m := rfl
  have hv : QMCLeafB.SimLoop.anyOk Rd.ok (Rd.K * Rd.m) = false := by
    rw [hKm]
    exact anyOk_all_false Rd.ok (P.K * P.m) (fun k hk => hok k hk)
  have hsound := QMCLeafB.SimLoop.simulate_refuted_sound (n := 2) (by norm_num)
    (QMCLeafB.wMatrix G₀) (-(1 / 2)) (QMCLeafB.EngineRuntime.Rq G₀ / 40000) Rd.dq Rd.cAq
    Rd.hdq Rd.hcAq Rd.hAsum Rd.ok Rd.cd Rd.hwit Rd.hrho Rd.hcne Rd.hdel0 Rd.hcheck
    Rd.hcut Rd.hrmax Rd.hle Rd.hhalve Rd.hbudget hv
  have hZ := hsound Z₀ Z₀_isUnitDiagPSD
  rw [trace_G₀_Z₀, Rq_G₀] at hZ
  norm_num at hZ

end QMCLeafB.ResidRefute

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.ResidRefute.univ_edge_two
#print axioms QMCLeafB.ResidRefute.Rq_G₀
#print axioms QMCLeafB.ResidRefute.Z₀_isUnitDiagPSD
#print axioms QMCLeafB.ResidRefute.trace_G₀_Z₀
#print axioms QMCLeafB.ResidRefute.anyOk_all_false
#print axioms QMCLeafB.ResidRefute.no_runParts_allFalse


