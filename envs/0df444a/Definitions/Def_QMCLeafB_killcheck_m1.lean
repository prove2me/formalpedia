-- Prove2me | Definitions.Def_QMCLeafB_killcheck_m1
-- name    : QMCLeafB_killcheck_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:49:59.552876+00:00
-- url     : https://prove2.me/theorems/03e12012-b835-4112-b8be-da77cfa4a9b1
-- title:
--   QMCLeafB killcheck_m1
-- statement:
--   # leaf B phase 19 — `killcheck` (swarm `smw1k12jb`, member m1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_closingAssembly_m3
import Definitions.Def_QMCLeafB_inhabit_m5
/-
# leaf B phase 19 — `killcheck` (swarm `smw1k12jb`, member m1)

**Independent machine-check of the residual's refutation.**  `Check_closingAssembly_m3` reduces the
leaf to `Resid o Pfam` — one `Bundle` per interior `(G, t)`, whose flag stream is all-`false`.  This
file proves that obligation **unsatisfiable at the campaign families**: the phase-18/19 residual
`Resid` is a false statement and cannot be supplied, so the `hmem`-elimination it encodes is not
available and the leaf's last mile has to keep the `RelaxMem` slot.

The argument is the analytic content of the loop, applied to the residual's own data:

* §1 `allFalse_floor` — from any `RunParts` whose flags are all `false`, `simulate_refuted_sound`
  (`Check_sim_loop_m6`) concludes that the threshold `t - Rq G/40000` lies under the trace floor of
  the unit-diagonal PSD set: `(t - Rq G/40000) ≤ trace(wMatrix G · Z)` for **every** unit-diagonal
  PSD `Z`.  The run's own `RunParams` supply the halving and fuel budgets; no extra hypothesis and
  no `hmem`-style slot is involved.
* §2 the one-edge instance `G0` (single edge of weight `1/2`, so `Rq G0 = 1`), threshold `t = -1/2`
  — strictly inside the interior bracket `[-1, -1/40000)` — and the point `Z₀ = v vᵀ` with
  `v = (1,-1)` (unit diagonal, PSD), for which `trace(wMatrix G0 · Z₀) = -1`, while
  `t - Rq G0/40000 = -1/2 - 1/40000 > -1`.  So no all-`false` run exists there.
* §3 `no_bundle_G0` and `resid_refuted` / `resid_refuted_guardT` — through
  `ClosingAssembly.runParts_of_bundle`, a `Bundle` at that instance yields such a run, hence
  `False`.  This holds at `UnionShallow.paramsKbc2` (the `round` stroke) and at
  `LoopClose.paramsShallow` (the `roundGT` stroke): both hypotheses of the closing's `solution` and
  `solution_guardT` are unsatisfiable.

What this leaves standing: `RunParts` itself is *not* refuted — only its all-`false` specialisation
is.  `DriftExact.runParts_of_exact_trace` already takes the `RelaxMem` slot `hmem` as an argument
and `InhabitM5.relaxMem_pinch`/`relaxMem_Gtwo` inhabit it at the pinch boundary, so the repair is
the phase-17 shape with `hmem` **kept**, not the phase-18 shape with it eliminated.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.KillCheckM1

open QuantumMaxCutEnergy

/-! ## 1.  An all-`false` run pushes the threshold under the trace floor -/

/-- **The floor theorem.**  If every round of a run answers `cut`, the loop's refutation certificate
is complete, and `simulate_refuted_sound` says the threshold sits under the trace floor. -/
theorem allFalse_floor {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hn : 2 ≤ G.n) (B : QMCLeafB.FinalStroke.RunParts o G t P)
    (hall : ∀ k, k < P.K * P.m → B.ok k = false) :
    ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z →
      (t : ℝ) - ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
        ≤ (QMCLeafB.wMatrix G * Z).trace := by
  have hv : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = false := by
    rw [QMCLeafB.SimLoop.anyOk_eq_false_iff]
    exact hall
  exact QMCLeafB.SimLoop.simulate_refuted_sound (hn := hn) (A := QMCLeafB.wMatrix G)
    (t := t) (εr := QMCLeafB.EngineRuntime.Rq G / 40000) (δq := P.dq) (cAq := P.cAq)
    (hδq := P.hdq) (hcAq := P.hcAq) (hAsum := P.hAsum) (ok := B.ok) (cd := B.cd)
    (hwit := B.hwit) (hρ := B.hrho) (hcne := B.hcne) (hδ0 := B.hdel0)
    (hcheck := B.hcheck) (hcutδ := B.hcut) (ρmax := P.rmax) (hρmax := P.hrmax)
    (hle := B.hle) (hm := P.hhalve) (hK := P.hbudget) (hv := hv)

#print axioms QMCLeafB.KillCheckM1.allFalse_floor

/-! ## 2.  The refuting instance

`G0`: two vertices, the single edge of weight `1/2`, so `Rq G0 = 2·(1/2) = 1`.  Its interior bracket
is `[-1, -1/40000)`; the threshold `t = -1/2` sits inside it.  The point `Z₀ = v vᵀ` with
`v = (1,-1)` is unit-diagonal PSD and pairs to `-1`, which is *below* `t - Rq/40000`. -/

/-- The refuting instance: two vertices, one edge of weight `1` (`Rq = 2`). -/
abbrev G0 : QuantumMaxCutEnergy.Input := QMCLeafB.InhabitM5.Gtwo

theorem Rq_G0 : QMCLeafB.EngineRuntime.Rq G0 = 2 := QMCLeafB.InhabitM5.Rq_Gtwo

theorem hn_G0 : 2 ≤ G0.n := by decide

theorem hn_ne_one : G0.n ≠ 1 := by decide

/-- A two-term sum at the instance's index type. -/
theorem sum2 {M : Type} [AddCommMonoid M] (f : Fin G0.n → M) : ∑ i, f i = f 0 + f 1 := by
  show (∑ i : Fin 2, f i) = f 0 + f 1
  exact Fin.sum_univ_two f

/-- The weight matrix's two off-diagonal entries are `1`. -/
theorem wMatrix_G0_01 :
    QMCLeafB.wMatrix G0 (0 : Fin G0.n) (1 : Fin G0.n) = 1 := by
  rw [QMCLeafB.wMatrix_apply_of_lt (by decide : (0 : Fin G0.n) < 1)]
  show (((1 : ℚ≥0)) : ℝ) = 1
  norm_num

theorem wMatrix_G0_10 :
    QMCLeafB.wMatrix G0 (1 : Fin G0.n) (0 : Fin G0.n) = 1 := by
  rw [QMCLeafB.wMatrix_apply_of_gt (by decide : (0 : Fin G0.n) < 1)]
  show (((1 : ℚ≥0)) : ℝ) = 1
  norm_num

/-- The refuting direction `v = (1, -1)`. -/
def v0 : Fin G0.n → ℝ := fun i => if (i : ℕ) = 0 then 1 else -1

/-- The refuting point `Z₀ = v vᵀ = !![1,-1;-1,1]`. -/
def Z0 : Matrix (Fin G0.n) (Fin G0.n) ℝ := Matrix.vecMulVec v0 (star v0)

theorem Z0_00 : Z0 (0 : Fin G0.n) (0 : Fin G0.n) = 1 := by
  simp [Z0, Matrix.vecMulVec_apply, v0]

theorem Z0_01 : Z0 (0 : Fin G0.n) (1 : Fin G0.n) = -1 := by
  simp [Z0, Matrix.vecMulVec_apply, v0, hn_ne_one]

theorem Z0_10 : Z0 (1 : Fin G0.n) (0 : Fin G0.n) = -1 := by
  simp [Z0, Matrix.vecMulVec_apply, v0, hn_ne_one]

theorem Z0_11 : Z0 (1 : Fin G0.n) (1 : Fin G0.n) = 1 := by
  simp [Z0, Matrix.vecMulVec_apply, v0, hn_ne_one]

/-- **`Z₀` is unit-diagonal PSD** — it is the Gram matrix of `v = (1,-1)`. -/
theorem Z0_isUnitDiagPSD : QMCLeafB.AnswerProducer.IsUnitDiagPSD Z0 := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star v0, fun i => ?_⟩
  fin_cases i
  · exact Z0_00
  · exact Z0_11

#print axioms QMCLeafB.KillCheckM1.Z0_isUnitDiagPSD

/-- The pairing of the instance's weight matrix with `Z₀` is `-2 = -Rq G0`. -/
theorem trace_G0_Z0 : (QMCLeafB.wMatrix G0 * Z0).trace = -2 := by
  have h0 : (QMCLeafB.wMatrix G0 * Z0) (0 : Fin G0.n) (0 : Fin G0.n) = -1 := by
    rw [Matrix.mul_apply, sum2,
      QMCLeafB.wMatrix_apply_of_eq, wMatrix_G0_01, Z0_00, Z0_10]
    norm_num
  have h1 : (QMCLeafB.wMatrix G0 * Z0) (1 : Fin G0.n) (1 : Fin G0.n) = -1 := by
    rw [Matrix.mul_apply, sum2,
      wMatrix_G0_10, QMCLeafB.wMatrix_apply_of_eq, Z0_01, Z0_11]
    norm_num
  rw [Matrix.trace]
  show (∑ i, (QMCLeafB.wMatrix G0 * Z0) i i) = -2
  rw [sum2, h0, h1]
  norm_num

#print axioms QMCLeafB.KillCheckM1.trace_G0_Z0

/-! ## 3.  No bundle at the instance, hence no residual -/

/-- **A `Bundle` at the refuting instance is impossible.**  `runParts_of_bundle` converts it into a
`RunParts` with the same all-`false` flags, and the floor theorem contradicts `Z₀`. -/
theorem no_bundle_G0 (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : QMCLeafB.FinalStroke.RunParams G0) (hn : 2 ≤ G0.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G0) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G0 ≤ QMCLeafB.RundataCert.eps G0)
    (B : QMCLeafB.ClosingAssembly.Bundle o G0 (-1) P hn) : False := by
  have hfloor := allFalse_floor hn
    (QMCLeafB.ClosingAssembly.runParts_of_bundle o G0 (-1) P hn hrmaxPos hrmax1 hbudP B)
    (fun k hk => B.hokAll k hk)
  have h := hfloor Z0 Z0_isUnitDiagPSD
  rw [trace_G0_Z0, Rq_G0] at h
  norm_num at h

#print axioms QMCLeafB.KillCheckM1.no_bundle_G0

/-- The threshold `-1/2` is in the interior bracket at `G0`. -/
theorem bracket_mem_G0 : -QMCLeafB.EngineRuntime.Rq G0 ≤ (-1 : ℚ) ∧
    ((-1 : ℚ) : ℝ)
      < -(((QMCLeafB.EngineRuntime.Rq G0 / 40000 : ℚ)) : ℝ) := by
  rw [Rq_G0]
  constructor <;> norm_num

#print axioms QMCLeafB.KillCheckM1.bracket_mem_G0

/-- **The phase-18/19 residual is refuted at the `round` family.**  `Resid` at
`UnionShallow.paramsKbc2` — the hypothesis of `ClosingAssembly.solution` — is unsatisfiable. -/
theorem resid_refuted (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (h : QMCLeafB.ClosingAssembly.Resid o QMCLeafB.UnionShallow.paramsKbc2) : False := by
  refine no_bundle_G0 o (QMCLeafB.UnionShallow.paramsKbc2 G0) hn_G0
    (QMCLeafB.ClosingAssembly.rmaxOf_pos G0 hn_G0)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one G0 hn_G0) ?_
    (h G0 (-1) hn_G0 bracket_mem_G0.1 bracket_mem_G0.2)
  exact QMCLeafB.ClosingAssembly.budget_dqShallow G0 hn_G0 (by rw [Rq_G0]; norm_num)

#print axioms QMCLeafB.KillCheckM1.resid_refuted

/-- **… and at the `roundGT` family**: `ClosingAssembly.solution_guardT`'s hypothesis is
unsatisfiable too. -/
theorem resid_refuted_guardT (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (h : QMCLeafB.ClosingAssembly.Resid o QMCLeafB.LoopClose.paramsShallow) : False := by
  refine no_bundle_G0 o (QMCLeafB.LoopClose.paramsShallow G0) hn_G0
    (QMCLeafB.GuardT.paramsShallow_rmax_pos hn_G0)
    (QMCLeafB.GuardT.paramsShallow_rmax_le_one hn_G0) ?_
    (h G0 (-1) hn_G0 bracket_mem_G0.1 bracket_mem_G0.2)
  exact QMCLeafB.GuardT.paramsShallow_budget hn_G0 (by rw [Rq_G0]; norm_num)

#print axioms QMCLeafB.KillCheckM1.resid_refuted_guardT

end QMCLeafB.KillCheckM1


