-- Prove2me | Definitions.Def_QMCLeafB_inhabit_m5
-- name    : QMCLeafB_inhabit_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:11:31.094196+00:00
-- url     : https://prove2.me/theorems/62b8dd38-4a31-45d4-b5b8-4b67057d5d9f
-- title:
--   QMCLeafB inhabit_m5
-- statement:
--   # leaf B phase 18 — brick `inhabit` (swarm `smw1i2drp`, member m5, direction d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_drift_m3
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 18 — brick `inhabit` (swarm `smw1i2drp`, member m5, direction d5)

The endgame's residual is the 14-item bundle that `DriftExact.runParts_at_interior_exact`
consumes (records `{C, hmarg, hmem, hCsym, hcEq, hcn, hcne}`, `hlam0-2`, `hTrc`, `hdriftc`,
`hdriftd`, `hverdict`).  A bundle with that many interlocking slots has a failure mode that no
amount of "does it prove the leaf" auditing catches: it can be **inconsistent**, in which case the
whole residual is vacuous and the campaign's last mile proves nothing.  This file settles that
question on the positive side, machine-checked:

* §1 `anyOk_true_succ` — the all-`ok` flag stream reads `true` at any positive count;
  `flatQ_one_apply`/`flatQ_one_ne_zero` — `flat 1` is a nonzero vector.
* §2 the pinch machinery in the direction the residuals need: `qf_smul`, `frob_smul`, and
  `relaxMem_pinch` — for a rational point `Q` with unit diagonal and nonnegative quadratic form,
  the boundary-lowered centre `(1 - δ/4) • Q` is a `RelaxMem` certificate at threshold `u` as soon
  as `(1 - δ/4) · frob A Q ≤ u + δ/2`.  This is the `(1 - dq/4)` pinch scale (NOT `(1 - dq/2)`,
  cf. phase-17 `Check_obstruction_m1`).
* §3 `nonempty_runParts_okTrue` — the structural reduction: on a run that never cuts
  (`ok ≡ true`), the 14 slots collapse to *three*: one `RelaxMem` certificate per round at the
  queried centre, `hCsym`, `hTrc`; `C`/`hmarg`/`hcEq`/`hlam1`/`hlam2`/`hdriftc`/`hdriftd` are
  vacuous and `hcn`/`hcne` are met by `c = 0`, `λ = 1`, `cn = flat 1`.
* §4 the concrete instance `Gtwo` (one edge of weight `1`, `n = 2`): `Rq Gtwo = 2`,
  `frob (wMatrixQ Gtwo) Q₀ = -2` for `Q₀ = !![1,-1;-1,1]`, `qf Q₀ ≥ 0`.  With
  `t := -Rq Gtwo + eps Gtwo` — strictly interior, `-Rq ≤ t < -eps` — the boundary centre
  `(1 - dq/4) • Q₀` satisfies the whole residual bundle, and the trace budget is attained with
  equality (the pinch).
* §5 `residual_inhabited_interior` — the summary: the residual of the leaf is **non-vacuous**.

Scope, stated honestly: this is consistency (inhabitation) of the residual, not a proof of it at a
general `G`.  The all-`ok` route is *instance-specific*: at `n = 2` the relaxation's optimum is
`-Rq`, which is exactly what the interior threshold `t - eps ≈ -Rq` needs.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; axiom audits at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.InhabitM5

open QuantumMaxCutEnergy
open QMCLeafB.SepOracle (qf frob)

/-! ## 1.  The all-`ok` flag stream, and `flat 1` -/

theorem anyOk_true_succ (m : ℕ) :
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) (m + 1) = true := rfl

/-- The all-`ok` stream has no `false` flag. -/
theorem okTrue_ne_false (k : ℕ) : (fun _ : ℕ => true) k ≠ false := by simp

/-- The diagonal read-out of `flat 1`: the diagonal index carries `1`. -/
theorem flatQ_one_apply {n : ℕ} (i : Fin n) :
    QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) (finProdFinEquiv (i, i)) = 1 := by
  have hs : finProdFinEquiv.symm (finProdFinEquiv (i, i)) = (i, i) := Equiv.symm_apply_apply _ _
  rw [show QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) (finProdFinEquiv (i, i))
      = (1 : Matrix (Fin n) (Fin n) ℚ) (finProdFinEquiv.symm (finProdFinEquiv (i, i))).1
          (finProdFinEquiv.symm (finProdFinEquiv (i, i))).2 from rfl, hs]
  rw [Matrix.one_apply, if_pos rfl]

/-- `flat 1` is a nonzero vector on a nonempty index set. -/
theorem flatQ_one_ne_zero {n : ℕ} (hn : 0 < n) :
    QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) ≠ 0 := by
  intro h
  have h0 := flatQ_one_apply (n := n) (⟨0, hn⟩ : Fin n)
  have h1 := congrFun h (finProdFinEquiv ((⟨0, hn⟩ : Fin n), (⟨0, hn⟩ : Fin n)))
  simp only [Pi.zero_apply] at h1
  rw [h0] at h1
  exact one_ne_zero h1

/-! ## 2.  The pinch centre: `(1 - δ/4) • Q` is a feasible point

`hdiagc` together with `RelaxMem.diag_near` pins the queried centre's diagonal to the boundary
`1 - dq/4`.  Here is the matching *construction*: any rational point `Q` with unit diagonal and
nonnegative quadratic form can be lowered to that boundary and stays a feasibility certificate, at
the threshold cost of the lowering. -/

/-- Scaling the matrix scales the quadratic form. -/
theorem qf_smul {n : ℕ} (c : ℚ) (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf (c • M) x = c * qf M x := by
  simp only [QMCLeafB.SepOracle.qf, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- Scaling the point scales the Frobenius pairing. -/
theorem frob_smul {n : ℕ} (c : ℚ) (A Q : Matrix (Fin n) (Fin n) ℚ) :
    frob A (c • Q) = c * frob A Q := by
  simp only [QMCLeafB.SepOracle.frob, Matrix.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- **The boundary-lowered centre is a `RelaxMem` certificate.**  `Q` supplies the shape (unit
diagonal, nonnegative quadratic form); `hfr` is the *only* quantitative cost — the lowered point
still has to be under the threshold `u + δ/2`. -/
theorem relaxMem_pinch {n : ℕ} (A Q : Matrix (Fin n) (Fin n) ℚ) {u δ : ℚ}
    (hδ : 0 < δ) (hδ4 : δ ≤ 4) (hQ : ∀ i, Q i i = 1) (hQq : ∀ x, 0 ≤ qf Q x)
    (hfr : (1 - δ / 4) * frob A Q ≤ u + δ / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A ((1 - δ / 4) • Q) u δ where
  δ_pos := hδ
  psd_margin := by
    intro x
    rw [qf_smul]
    have h1 : 0 ≤ qf Q x := hQq x
    have h2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    have h3 : 0 ≤ 1 - δ / 4 := by linarith
    nlinarith
  diag_near := by
    intro i
    have hii : ((1 - δ / 4) • Q) i i = 1 - δ / 4 := by
      simp only [Matrix.smul_apply, hQ i, smul_eq_mul, mul_one]
    rw [hii]
    have hsub : (1 - δ / 4) - 1 = -(δ / 4) := by ring
    rw [hsub, abs_neg, abs_of_pos (by linarith : (0 : ℚ) < δ / 4)]
  trace_le := by
    rw [frob_smul]
    exact hfr

/-! ## 3.  A run that never cuts: the 14-slot bundle collapses to three -/

/-- **Inhabitation of the residual bundle on an all-`ok` run.**  Given one `RelaxMem` certificate
per round at the queried centre, the symmetry of the centres and the trace budget, the whole
residual of `runParts_at_interior_exact` is discharged.  The vacuous slots are instantiated by the
canonical choices `c = 0`, `λ = 1`, `cn = flat 1` (`hcn` reads `flat 1 = flat 1`, and `hcne` is
`flat 1 ≠ 0`). -/
theorem nonempty_runParts_okTrue
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hverdict : o G t = true)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hMem : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hTrc : ∀ k, ∑ i, cX k i i
      ≤ (G.n : ℚ) * (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) := by
  classical
  have hpos : 0 < (QMCLeafB.UnionShallow.paramsKbc2 G).K
      * (QMCLeafB.UnionShallow.paramsKbc2 G).m :=
    lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul G)
  have hany : QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m) = true := by
    conv_lhs => rw [show (QMCLeafB.UnionShallow.paramsKbc2 G).K
      * (QMCLeafB.UnionShallow.paramsKbc2 G).m
        = ((QMCLeafB.UnionShallow.paramsKbc2 G).K
            * (QMCLeafB.UnionShallow.paramsKbc2 G).m - 1) + 1 from by omega]
    exact anyOk_true_succ _
  have hne : ∀ k : ℕ, QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ≠ 0 :=
    fun _ => flatQ_one_ne_zero (by omega)
  refine ⟨QMCLeafB.DriftExact.runParts_at_interior_exact o G t hn hRq
    (fun _ => true) (fun _ => 1) cX (fun _ => 1) (fun _ _ => 0)
    (fun _ => QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (fun k hok => absurd hok (okTrue_ne_false k)) ?_ ?_ hCsym ?_ ?_ hne ?_ ?_ ?_ hTrc ?_ ?_ ?_⟩
  · intro k hok
    exact absurd hok (okTrue_ne_false k)
  · intro k hk _
    exact hMem k hk
  · intro k hok
    exact absurd hok (okTrue_ne_false k)
  · intro k
    show QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
      = (0 : Fin (G.n * G.n) → ℚ) + (1 : ℚ) • QMCLeafB.RelaxOracle.flatQ 1
    simp
  · intro k
    norm_num
  · intro k hok
    exact absurd hok (okTrue_ne_false k)
  · intro k hok
    exact absurd hok (okTrue_ne_false k)
  · intro k hok
    exact absurd hok (okTrue_ne_false k)
  · intro k hok
    exact absurd hok (okTrue_ne_false k)
  · rw [hverdict, hany]

/-! ## 4.  The concrete instance: one edge of weight `1` on two vertices -/

/-- The two-vertex, one-edge graph of weight `1`. -/
def Gtwo : QuantumMaxCutEnergy.Input := ⟨2, fun _ => 1⟩

instance : NeZero Gtwo.n := ⟨by decide⟩

/-- The unique edge of `Edge 2`. -/
def e2 : QuantumMaxCutEnergy.Edge 2 := ⟨(0, 1), by decide⟩

theorem edge2_unique (e : QuantumMaxCutEnergy.Edge 2) : e = e2 := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · refine Fin.ext ?_
    have h1 : ((e.val.1 : Fin 2) : ℕ) < 2 := e.val.1.isLt
    have h2 : ((e.val.2 : Fin 2) : ℕ) < 2 := e.val.2.isLt
    have hlt : ((e.val.1 : Fin 2) : ℕ) < ((e.val.2 : Fin 2) : ℕ) := e.2
    show ((e.val.1 : Fin 2) : ℕ) = 0
    omega
  · refine Fin.ext ?_
    have h1 : ((e.val.1 : Fin 2) : ℕ) < 2 := e.val.1.isLt
    have h2 : ((e.val.2 : Fin 2) : ℕ) < 2 := e.val.2.isLt
    have hlt : ((e.val.1 : Fin 2) : ℕ) < ((e.val.2 : Fin 2) : ℕ) := e.2
    show ((e.val.2 : Fin 2) : ℕ) = 1
    omega

/-- The campaign's energy scale at the one-edge instance: `Rq = 2·Σ w = 2`. -/
theorem Rq_Gtwo : QMCLeafB.EngineRuntime.Rq Gtwo = 2 := by
  have huniv : (Finset.univ : Finset (QuantumMaxCutEnergy.Edge 2)) = {e2} := by
    ext b
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact edge2_unique b
  have h : (∑ e : QuantumMaxCutEnergy.Edge 2, ((Gtwo.weights e : ℚ≥0) : ℚ)) = 1 := by
    rw [huniv, Finset.sum_singleton]
    rfl
  show 2 * (∑ e : QuantumMaxCutEnergy.Edge 2, ((Gtwo.weights e : ℚ≥0) : ℚ)) = 2
  rw [h]
  norm_num

/-- A two-term sum at the instance's index type. -/
theorem sum_inst {M : Type} [AddCommMonoid M] (f : Fin Gtwo.n → M) :
    ∑ i, f i = f 0 + f 1 := by
  show (∑ i : Fin 2, f i) = f 0 + f 1
  exact Fin.sum_univ_two f

/-- The `n = 2` block `[[1,-1],[-1,1]]`: unit diagonal, nonnegative quadratic form, and its pairing
with the adjacency matrix of one edge is `-2 = -Rq`. -/
def Q0 : Matrix (Fin Gtwo.n) (Fin Gtwo.n) ℚ := !![1, -1; -1, 1]

theorem Q0_00 : Q0 (0 : Fin Gtwo.n) (0 : Fin Gtwo.n) = 1 := by decide

theorem Q0_01 : Q0 (0 : Fin Gtwo.n) (1 : Fin Gtwo.n) = -1 := by decide

theorem Q0_10 : Q0 (1 : Fin Gtwo.n) (0 : Fin Gtwo.n) = -1 := by decide

theorem Q0_11 : Q0 (1 : Fin Gtwo.n) (1 : Fin Gtwo.n) = 1 := by decide

theorem Q0_diag (i : Fin Gtwo.n) : Q0 i i = 1 := by
  fin_cases i <;> decide

/-- `Q₀` is a nonnegative quadratic form: `qf Q₀ x = (x₀ - x₁)²`. -/
theorem Q0_qf (x : Fin Gtwo.n → ℚ) : 0 ≤ qf Q0 x := by
  have h : qf Q0 x = (x 0 - x 1) ^ 2 := by
    simp only [QMCLeafB.SepOracle.qf, Matrix.mulVec, dotProduct]
    simp only [sum_inst]
    rw [Q0_00, Q0_01, Q0_10, Q0_11]
    ring
  rw [h]
  exact sq_nonneg _

theorem Q0_symm : Q0ᵀ = Q0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem wG_two_00 :
    QMCLeafB.Finalization.wMatrixQ Gtwo (0 : Fin Gtwo.n) (0 : Fin Gtwo.n) = 0 := by decide

theorem wG_two_01 :
    QMCLeafB.Finalization.wMatrixQ Gtwo (0 : Fin Gtwo.n) (1 : Fin Gtwo.n) = 1 := by decide

theorem wG_two_10 :
    QMCLeafB.Finalization.wMatrixQ Gtwo (1 : Fin Gtwo.n) (0 : Fin Gtwo.n) = 1 := by decide

theorem wG_two_11 :
    QMCLeafB.Finalization.wMatrixQ Gtwo (1 : Fin Gtwo.n) (1 : Fin Gtwo.n) = 0 := by decide

/-- The pairing of the one-edge adjacency matrix with `Q₀`: `-2 = -Rq Gtwo`. -/
theorem frob_Gtwo_Q0 : frob (QMCLeafB.Finalization.wMatrixQ Gtwo) Q0 = -2 := by
  simp only [QMCLeafB.SepOracle.frob]
  rw [sum_inst, sum_inst, sum_inst]
  rw [wG_two_00, wG_two_01, wG_two_10, wG_two_11, Q0_00, Q0_01, Q0_10, Q0_11]
  norm_num

/-! ### 4.1  The instance's numbers -/

/-- The instance threshold: `t := -Rq + eps`, strictly inside the interior bracket. -/
def tTwo : ℚ := -QMCLeafB.EngineRuntime.Rq Gtwo + QMCLeafB.RundataCert.eps Gtwo

theorem eps_Gtwo : QMCLeafB.RundataCert.eps Gtwo = 1 / 20000 := by
  unfold QMCLeafB.RundataCert.eps
  rw [Rq_Gtwo]
  norm_num

theorem tTwo_lower : -QMCLeafB.EngineRuntime.Rq Gtwo ≤ tTwo := by
  unfold tTwo
  have h := QMCLeafB.RundataCert.eps_nonneg Gtwo
  linarith

theorem tTwo_upper : (tTwo : ℝ) < -((QMCLeafB.RundataCert.eps Gtwo : ℚ) : ℝ) := by
  unfold tTwo
  rw [Rq_Gtwo, eps_Gtwo]
  norm_num

theorem dq_Gtwo_pos : 0 < (QMCLeafB.UnionShallow.paramsKbc2 Gtwo).dq := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  exact QMCLeafB.RundataParams.dqShallow_pos Gtwo

theorem dq_Gtwo_le_four : (QMCLeafB.UnionShallow.paramsKbc2 Gtwo).dq ≤ 4 := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  have h := QMCLeafB.UnionShallow.dqShallow_le_one Gtwo (by rw [Rq_Gtwo]; norm_num)
  linarith

/-- The queried centres of the all-`ok` run: the boundary-lowered `Q₀`, constant in `k`. -/
def cXtwo : ℕ → Matrix (Fin Gtwo.n) (Fin Gtwo.n) ℚ :=
  fun _ => (1 - (QMCLeafB.UnionShallow.paramsKbc2 Gtwo).dq / 4) • Q0

/-- **The ok-round certificate at the pinch boundary.** -/
theorem relaxMem_Gtwo (k : ℕ) :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ Gtwo) (cXtwo k)
      (tTwo - QMCLeafB.RundataCert.eps Gtwo) (QMCLeafB.UnionShallow.paramsKbc2 Gtwo).dq := by
  refine relaxMem_pinch _ Q0 dq_Gtwo_pos dq_Gtwo_le_four Q0_diag Q0_qf ?_
  rw [frob_Gtwo_Q0]
  have h : (1 - (QMCLeafB.UnionShallow.paramsKbc2 Gtwo).dq / 4) * (-2)
      = (tTwo - QMCLeafB.RundataCert.eps Gtwo)
        + (QMCLeafB.UnionShallow.paramsKbc2 Gtwo).dq / 2 := by
    unfold tTwo
    rw [Rq_Gtwo]
    ring
  rw [h]

/-- The centres are symmetric. -/
theorem hCsym_Gtwo (k : ℕ) : (cXtwo k)ᵀ = cXtwo k := by
  simp only [cXtwo, Matrix.transpose_smul, Q0_symm]

/-- **The trace budget, attained with equality**: the diagonal read-out sits exactly on `1 - dq/4`,
which is the pinch. -/
theorem hTrc_Gtwo (k : ℕ) : ∑ i, cXtwo k i i
    ≤ (Gtwo.n : ℚ) * (1 - (QMCLeafB.UnionShallow.paramsKbc2 Gtwo).dq / 4) := by
  have h : ∑ i, cXtwo k i i
      = 2 * (1 - (QMCLeafB.UnionShallow.paramsKbc2 Gtwo).dq / 4) := by
    rw [sum_inst]
    simp only [cXtwo, Matrix.smul_apply, Q0_00, Q0_11, smul_eq_mul, mul_one]
    ring
  rw [h]
  have hn : ((Gtwo.n : ℕ) : ℚ) = 2 := by
    show ((2 : ℕ) : ℚ) = 2
    norm_num
  rw [hn]

/-! ## 5.  The residual is inhabited at a strictly interior point -/

/-- **Non-vacuity of the last two residuals.**  At the one-edge, `n = 2` instance and the strictly
interior threshold `t = -Rq + eps` (so `-Rq ≤ t < -eps`, the bracket `hd` ranges over), the whole
`RunParts` bundle at `paramsKbc2` is inhabited — by the all-`ok` run whose queried centres are the
pinch boundary `(1 - dq/4) • Q₀`. -/
theorem residual_inhabited_interior :
    ∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq Gtwo ≤ t
      ∧ (t : ℝ) < -((QMCLeafB.RundataCert.eps Gtwo : ℚ) : ℝ)
      ∧ Nonempty (QMCLeafB.FinalStroke.RunParts (fun _ _ => true) Gtwo t
          (QMCLeafB.UnionShallow.paramsKbc2 Gtwo)) := by
  refine ⟨tTwo, tTwo_lower, tTwo_upper, ?_⟩
  refine nonempty_runParts_okTrue (fun _ _ => true) Gtwo tTwo (by decide) ?_ rfl cXtwo ?_ hCsym_Gtwo
    hTrc_Gtwo
  · rw [Rq_Gtwo]
    norm_num
  · intro k _
    exact relaxMem_Gtwo k

end QMCLeafB.InhabitM5

/-! ## Axiom audit -/

#print axioms QMCLeafB.InhabitM5.anyOk_true_succ
#print axioms QMCLeafB.InhabitM5.flatQ_one_ne_zero
#print axioms QMCLeafB.InhabitM5.qf_smul
#print axioms QMCLeafB.InhabitM5.frob_smul
#print axioms QMCLeafB.InhabitM5.relaxMem_pinch
#print axioms QMCLeafB.InhabitM5.nonempty_runParts_okTrue
#print axioms QMCLeafB.InhabitM5.Rq_Gtwo
#print axioms QMCLeafB.InhabitM5.frob_Gtwo_Q0
#print axioms QMCLeafB.InhabitM5.relaxMem_Gtwo
#print axioms QMCLeafB.InhabitM5.hTrc_Gtwo
#print axioms QMCLeafB.InhabitM5.residual_inhabited_interior


