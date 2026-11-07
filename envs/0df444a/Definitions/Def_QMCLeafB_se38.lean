-- Prove2me | Definitions.Def_QMCLeafB_se38
-- name    : QMCLeafB_se38
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:52:00.064195+00:00
-- url     : https://prove2.me/theorems/987b4982-2a4d-4821-b499-3a8ecd3bd9a4
-- title:
--   QMCLeafB se38
-- statement:
--   # `Check_se38_m4` — phase 38, member m4, direction `steering-exists`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_asm37
/-
# `Check_se38_m4` — phase 38, member m4, direction `steering-exists`

**The obligation under test.**  With `Cat_k` the accumulated point, `A_k` the current shape and
`σ_k = ‖c_k‖²_{A_k⁻¹}`, the collar's all-cut identity is the SHALLOW-CUT / bounded-distance
statement `sup_{z ∈ body} c_k·(Cat_k − z) ≤ rmax·√σ_k` at every round `k < K·m`.  This file takes
the constructive route: **exhibit the cut sequence**.

**What is proved here (machine-checked, no hypothesis on the programme).**

* §1–§2 **the fixed-direction stream and its exact shape law.**  Depth `ρ ≡ P.rmax`, normal
  `c_k ≡ v` (a FIXED nonzero rational direction), exact witness `p_k = (M q^{2k}) • v` with
  `M = 2n² + 2dq²` and `q = (N+ρ)/(N+1)`.  Because `A_0 = M⁻¹ • 1` is a multiple of the identity, `v`
  is an eigenvector of **every** iterate: `A_k *ᵥ v = (M q^{2k})⁻¹ • v`
  (`Aat_cdF_mulVec`), and the recorded witness satisfies `A_k *ᵥ p_k = c_k` (`cdF_wit`).
  The scalar identities behind this are `γ = 1 − q` (`one_sub_qOf`) and `α(1+β) = q⁻²`
  (`alphaQ_one_add_betaQ`), both valid at EVERY depth `ρ ∈ [0,1)` — the depth ledger is not what
  fixes the geometry.

* §3 **the exact centre law** (`Cat_cdF_dot`): along this stream the accumulated centre's coordinate
  in the cut direction is EXACTLY `v ⬝ Cat_k = D·(1 − q^k)`, with `D = √(M·|v|²)` the initial
  `v`-radius of the ellipsoid.  The centre travels monotonically toward the body and its total reach
  is `D` — independent of the depth and of the round count.

* §4 **the reach theorem** (`bodyRec_of_reach`): if the relaxation lies above a level
  `b ≥ D·(1 − q^{K·m})` in some rational direction `v` — i.e. **the body is beyond the centre's
  `K·m`-round reach** — then the all-false record EXISTS, with margin `del ≡ 0`.  So the depth ledger
  `del² ≤ ρ²σ` is discharged with room to spare and the shallow-cut inequality holds with the sharper
  constant `0` instead of `rmax·√σ_k`.

* §5 **consequences**: `ReachThin ⟹ BodyRec ⟹ Nonempty (RunParts o G t P)` at every bit that reads
  `false` there, and a `CollarRec`-shaped reduction.

**The verdict this file supports.**  The inequality IS achievable by a cut sequence — but only for
bodies beyond the centre's reach.  The reach `D(1 − q^{K·m})` is a fixed fraction of `D` whenever
`q^{K·m}` is small, so a body sitting at `0.7·D` (the `(G₁,tStar)` collar) lies INSIDE the reach and
this stream cannot serve it.  That is the exact sense in which the collar stands: the obstruction is
neither the depth ledger (`del ≡ 0` voids it) nor the programme — it is the ratio
`(distance from the initial centre to the body)/(initial radius)`.  The complementary mechanism is
banked (`BallM2.no_runParts_of_ball`, `Asm36M8.no_runParts_of_ball_horizon`: a body carrying a horizon
ball admits no record at all), so the record class is squeezed between "beyond the reach" (this file)
and "carrying a horizon ball" (banked).

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every load-bearing declaration.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Se38M4

open QMCLeafB.EngineIterates

/-! ## 1.  The constants of the fixed-direction stream -/

/-- `q = (N+ρ)/(N+1)`: the per-round contraction of the `v`-radius under a cut in direction `v`
at depth `ρ`. -/
def qOf (N : ℕ) (ρ : ℚ) : ℚ := ((N : ℚ) + ρ) / ((N : ℚ) + 1)

/-- The eigenvalue of the `k`-th shape on the cut direction: `μ_k = (M q^{2k})⁻¹`. -/
def muOf (N : ℕ) (M ρ : ℚ) (k : ℕ) : ℚ := (M * (qOf N ρ) ^ (2 * k))⁻¹

/-- **The fixed-direction transcript**: normal `v`, exact witness `μ_k⁻¹ • v`, depth `ρ`. -/
def cdF (N : ℕ) (M ρ : ℚ) (v : Fin N → ℚ) : ℕ → CutData N :=
  fun k => ⟨v, (M * (qOf N ρ) ^ (2 * k)) • v, ρ⟩

theorem cdF_c (N : ℕ) (M ρ : ℚ) (v : Fin N → ℚ) (k : ℕ) :
    (cdF N M ρ v k).c = v := rfl

theorem cdF_p (N : ℕ) (M ρ : ℚ) (v : Fin N → ℚ) (k : ℕ) :
    (cdF N M ρ v k).p = (M * (qOf N ρ) ^ (2 * k)) • v := rfl

theorem cdF_rho (N : ℕ) (M ρ : ℚ) (v : Fin N → ℚ) (k : ℕ) :
    (cdF N M ρ v k).rho = ρ := rfl

/-- The cut norm of the stream, in closed form. -/
theorem sigmaQ_cdF (N : ℕ) (M ρ : ℚ) (v : Fin N → ℚ) (k : ℕ) :
    sigmaQ v ((M * (qOf N ρ) ^ (2 * k)) • v)
      = M * (qOf N ρ) ^ (2 * k) * (v ⬝ᵥ v) := by
  unfold sigmaQ
  rw [dotProduct_smul, smul_eq_mul]

/-- `v ⬝ᵥ v > 0` for a nonzero rational vector. -/
theorem dotProduct_self_pos {N : ℕ} {v : Fin N → ℚ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have hpos : 0 < ∑ j, v j * v j := by
    refine Finset.sum_pos' (fun j _ => mul_self_nonneg (v j)) ?_
    by_contra hc
    push_neg at hc
    refine hv (funext fun j => ?_)
    have h1 : v j * v j ≤ 0 := hc j (Finset.mem_univ j)
    have h2 : 0 ≤ v j * v j := mul_self_nonneg (v j)
    exact mul_self_eq_zero.mp (le_antisymm h1 h2)
  simpa [dotProduct] using hpos

/-- `γ = 1 − q` at every depth: the centre's step factor is the complement of the contraction. -/
theorem one_sub_qOf (N : ℕ) (ρ : ℚ) : 1 - qOf N ρ = (1 - ρ) / ((N : ℚ) + 1) := by
  unfold qOf
  have h : ((N : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **`α (1 + β) = q⁻²`** — the scalar identity that makes a fixed direction an eigenvector of every
iterate.  Valid at every depth `ρ ≥ 0`, at every `N ≥ 2`. -/
theorem alphaQ_one_add_betaQ {N : ℕ} (hN : 2 ≤ N) {ρ : ℚ} (hρ : 0 ≤ ρ) :
    QMCLeafB.EngineIterates.alphaQ N ρ * (1 + QMCLeafB.EngineIterates.betaQ N)
      = (qOf N ρ)⁻¹ ^ 2 := by
  unfold QMCLeafB.EngineIterates.alphaQ QMCLeafB.EngineIterates.betaQ qOf
  have hN1 : ((N : ℚ) - 1) ≠ 0 := by
    have h2 : (2 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
    linarith
  have hNρ : ((N : ℚ) + ρ) ≠ 0 := by
    have h2 : (0 : ℚ) < (N : ℚ) := by positivity
    linarith
  have hN1' : ((N : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- `q` is positive. -/
theorem qOf_pos {N : ℕ} (hN : 1 ≤ N) {ρ : ℚ} (hρ : 0 ≤ ρ) : 0 < qOf N ρ := by
  unfold qOf
  have h1 : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have h2 : (0 : ℚ) < (N : ℚ) + 1 := by linarith
  positivity

/-- `q` is below one as soon as the depth is below one. -/
theorem qOf_lt_one {N : ℕ} {ρ : ℚ} (hρ : ρ < 1) : qOf N ρ < 1 := by
  unfold qOf
  have h1 : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  rw [div_lt_one h1]
  linarith

/-- The eigenvalue recursion. -/
theorem muOf_succ {N : ℕ} (hN : 2 ≤ N) {M ρ : ℚ} (hM : M ≠ 0) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (k : ℕ) :
    muOf N M ρ (k + 1) = QMCLeafB.EngineIterates.alphaQ N ρ
      * (1 + QMCLeafB.EngineIterates.betaQ N) * muOf N M ρ k := by
  have hq : qOf N ρ ≠ 0 := ne_of_gt (qOf_pos (by omega) hρ0)
  have hq2 : (qOf N ρ ^ 2)⁻¹ = QMCLeafB.EngineIterates.alphaQ N ρ
      * (1 + QMCLeafB.EngineIterates.betaQ N) := by
    rw [alphaQ_one_add_betaQ hN hρ0, inv_pow]
  have hid : qOf N ρ ^ (2 * (k + 1)) = qOf N ρ ^ (2 * k) * qOf N ρ ^ 2 := by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
  unfold muOf
  rw [hid]
  simp only [mul_inv, hq2]
  ring

/-! ## 2.  The eigenvector law: the shape never rotates the cut direction -/

theorem initShapeOf_mulVec (N : ℕ) (M : ℚ) (v : Fin N → ℚ) :
    QMCLeafB.Boundary.initShapeOf N M *ᵥ v = M⁻¹ • v := by
  unfold QMCLeafB.Boundary.initShapeOf
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **The step law at a fixed direction.**  If the cut direction `v` is an eigenvector of the shape
with eigenvalue `μ_k`, then the engine's own step keeps it an eigenvector, with eigenvalue `μ_{k+1}`. -/
theorem rStep_mulVec_cdF (N : ℕ) (hN : 2 ≤ N) {M ρ : ℚ} (hM : M ≠ 0) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {v : Fin N → ℚ} (hv : v ≠ 0) {A : Matrix (Fin N) (Fin N) ℚ} {k : ℕ}
    (hA : A *ᵥ v = muOf N M ρ k • v) :
    rStep N A v ((M * qOf N ρ ^ (2 * k)) • v) ρ *ᵥ v = muOf N M ρ (k + 1) • v := by
  have hs : v ⬝ᵥ v ≠ 0 := ne_of_gt (dotProduct_self_pos hv)
  have hqn : qOf N ρ ≠ 0 := ne_of_gt (qOf_pos (by omega) hρ0)
  have hMq : M * qOf N ρ ^ (2 * k) ≠ 0 := mul_ne_zero hM (pow_ne_zero _ hqn)
  have hvec : Matrix.vecMulVec v v *ᵥ v = (v ⬝ᵥ v) • v := by
    simpa using Matrix.vecMulVec_mulVec v v v
  unfold rStep
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, hvec, hA, sigmaQ_cdF]
  have hcoef : (QMCLeafB.EngineIterates.betaQ N
        / (M * qOf N ρ ^ (2 * k) * (v ⬝ᵥ v))) * (v ⬝ᵥ v)
      = QMCLeafB.EngineIterates.betaQ N * muOf N M ρ k := by
    unfold muOf
    field_simp
  rw [smul_smul, hcoef, ← add_smul, smul_smul]
  rw [show muOf N M ρ (k + 1) = QMCLeafB.EngineIterates.alphaQ N ρ
      * (1 + QMCLeafB.EngineIterates.betaQ N) * muOf N M ρ k
    from muOf_succ hN hM hρ0 hρ1 k]
  congr 1
  ring

/-- **The eigenvector law.**  Along the fixed-direction stream the cut vector stays an eigenvector of
every iterate, with eigenvalue `μ_k = (M q^{2k})⁻¹`. -/
theorem Aat_cdF_mulVec (N : ℕ) (hN : 2 ≤ N) {M ρ : ℚ} (hM : 0 < M) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {v : Fin N → ℚ} (hv : v ≠ 0) :
    ∀ k, Aat N (QMCLeafB.Boundary.initShapeOf N M) (cdF N M ρ v) k *ᵥ v
      = muOf N M ρ k • v := by
  intro k
  induction k with
  | zero =>
    rw [show Aat N (QMCLeafB.Boundary.initShapeOf N M) (cdF N M ρ v) 0
        = QMCLeafB.Boundary.initShapeOf N M from rfl, initShapeOf_mulVec]
    congr 1
    unfold muOf
    simp
  | succ k ih =>
    rw [Aat_unfold]
    exact rStep_mulVec_cdF N hN (ne_of_gt hM) hρ0 hρ1 hv ih

/-- The witness relation the record needs (`hwit`), in closed form. -/
theorem cdF_wit (N : ℕ) (hN : 2 ≤ N) {M ρ : ℚ} (hM : 0 < M) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {v : Fin N → ℚ} (hv : v ≠ 0) (k : ℕ) :
    Aat N (QMCLeafB.Boundary.initShapeOf N M) (cdF N M ρ v) k *ᵥ (cdF N M ρ v k).p
      = (cdF N M ρ v k).c := by
  have hqn : qOf N ρ ≠ 0 := ne_of_gt (qOf_pos (by omega) hρ0)
  have hMq : M * qOf N ρ ^ (2 * k) ≠ 0 := mul_ne_zero (ne_of_gt hM) (pow_ne_zero _ hqn)
  show Aat N (QMCLeafB.Boundary.initShapeOf N M) (cdF N M ρ v) k
      *ᵥ ((M * qOf N ρ ^ (2 * k)) • v) = v
  rw [Matrix.mulVec_smul, Aat_cdF_mulVec N hN hM hρ0 hρ1 hv k, smul_smul]
  rw [show M * qOf N ρ ^ (2 * k) * muOf N M ρ k = 1 by
    unfold muOf
    exact mul_inv_cancel₀ hMq, one_smul]

#print axioms QMCLeafB.Se38M4.sigmaQ_cdF
#print axioms QMCLeafB.Se38M4.Aat_cdF_mulVec
#print axioms QMCLeafB.Se38M4.cdF_wit

/-! ## 3.  The exact centre law over `ℝ` -/

/-- The real cast of a rational direction. -/
def vR {N : ℕ} (v : Fin N → ℚ) : Fin N → ℝ := fun i => ((v i : ℚ) : ℝ)

/-- `D = √(M·|v|²)`: the initial `v`-radius of the ellipsoid, in the `v`-coordinate scale. -/
def reachD {N : ℕ} (M : ℚ) (v : Fin N → ℚ) : ℝ :=
  Real.sqrt ((M : ℝ) * (vR v ⬝ᵥ vR v))

theorem vR_dot_self {N : ℕ} (v : Fin N → ℚ) :
    vR v ⬝ᵥ vR v = ((v ⬝ᵥ v : ℚ) : ℝ) := by
  simp [vR, dotProduct, Rat.cast_sum, Rat.cast_mul]

theorem reachD_sq (N : ℕ) {M : ℚ} (hM : 0 < M) {v : Fin N → ℚ} (hv : v ≠ 0) :
    reachD M v ^ 2 = (M : ℝ) * (vR v ⬝ᵥ vR v) := by
  rw [reachD, Real.sq_sqrt]
  have h1 : (0 : ℚ) < v ⬝ᵥ v := dotProduct_self_pos hv
  have h2 : (0 : ℝ) < (vR v ⬝ᵥ vR v) := by
    rw [vR_dot_self]
    exact_mod_cast h1
  have h3 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  positivity

theorem reachD_pos (N : ℕ) {M : ℚ} (hM : 0 < M) {v : Fin N → ℚ} (hv : v ≠ 0) :
    0 < reachD M v := by
  rw [reachD, Real.sqrt_pos]
  have h1 : (0 : ℚ) < v ⬝ᵥ v := dotProduct_self_pos hv
  have h2 : (0 : ℝ) < (vR v ⬝ᵥ vR v) := by
    rw [vR_dot_self]
    exact_mod_cast h1
  have h3 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  positivity

/-- The cut norm along the stream, over `ℝ`, in closed form. -/
theorem sigmaR_cdF {N : ℕ} (M ρ : ℚ) (v : Fin N → ℚ) (k : ℕ) :
    sigmaR (vR v) (vR ((M * (qOf N ρ) ^ (2 * k)) • v))
      = (M : ℝ) * (((qOf N ρ : ℚ) : ℝ)) ^ (2 * k) * (vR v ⬝ᵥ vR v) := by
  have hcast : ((sigmaQ v ((M * (qOf N ρ) ^ (2 * k)) • v) : ℚ) : ℝ)
      = sigmaR (vR v) (vR ((M * (qOf N ρ) ^ (2 * k)) • v)) := cast_sigmaQ _ _
  rw [← hcast, sigmaQ_cdF]
  push_cast
  rw [vR_dot_self]

/-- The `√σ` of the stream, in closed form: `√σ_k = D q^k`. -/
theorem sqrtSigmaR_cdF (N : ℕ) (hN : 1 ≤ N) {M ρ : ℚ} (hM : 0 < M) (hρ : 0 ≤ ρ)
    {v : Fin N → ℚ} (hv : v ≠ 0) (k : ℕ) :
    sqrtSigmaR (vR v) (vR ((M * (qOf N ρ) ^ (2 * k)) • v))
      = reachD M v * (((qOf N ρ : ℚ) : ℝ)) ^ k := by
  have hq0 : (0 : ℚ) < qOf N ρ := qOf_pos hN hρ
  have hD0 : (0 : ℝ) ≤ reachD M v := le_of_lt (reachD_pos N hM hv)
  have hsq : reachD M v ^ 2 = (M : ℝ) * (vR v ⬝ᵥ vR v) := reachD_sq N hM hv
  unfold sqrtSigmaR
  rw [sigmaR_cdF]
  have hkey : (M : ℝ) * ((qOf N ρ : ℚ) : ℝ) ^ (2 * k) * (vR v ⬝ᵥ vR v)
      = (reachD M v * ((qOf N ρ : ℚ) : ℝ) ^ k) ^ 2 := by
    rw [mul_pow, hsq]
    ring
  rw [hkey, Real.sqrt_sq (by positivity)]

/-- The witness of the stream, in the flat real shape. -/
theorem cutPR_cdF (N : ℕ) (M ρ : ℚ) (v : Fin N → ℚ) (k : ℕ) :
    cutPR (cdF N M ρ v) k = ((M : ℝ) * ((qOf N ρ : ℚ) : ℝ) ^ (2 * k)) • vR v := by
  funext i
  simp [cutPR, cdF_p, vR, Rat.cast_mul, Rat.cast_pow]

/-- The cut norm, in the applied form. -/
theorem sigmaR_cdF_apply (N : ℕ) (M ρ : ℚ) (v : Fin N → ℚ) (k : ℕ) :
    sigmaR (vR v) (((M : ℝ) * ((qOf N ρ : ℚ) : ℝ) ^ (2 * k)) • vR v)
      = (M : ℝ) * ((qOf N ρ : ℚ) : ℝ) ^ (2 * k) * (vR v ⬝ᵥ vR v) := by
  rw [← cutPR_cdF]
  exact sigmaR_cdF M ρ v k

/-- The `√σ` of the stream, in the applied form. -/
theorem sqrtSigmaR_cdF_apply (N : ℕ) (hN : 1 ≤ N) {M ρ : ℚ} (hM : 0 < M) (hρ : 0 ≤ ρ)
    {v : Fin N → ℚ} (hv : v ≠ 0) (k : ℕ) :
    sqrtSigmaR (vR v) (((M : ℝ) * ((qOf N ρ : ℚ) : ℝ) ^ (2 * k)) • vR v)
      = reachD M v * (((qOf N ρ : ℚ) : ℝ)) ^ k := by
  rw [← cutPR_cdF]
  exact sqrtSigmaR_cdF N hN hM hρ hv k

/-- **The step of the centre along the cut direction.** -/
theorem Cat_cdF_step (N : ℕ) (hN : 2 ≤ N) {M ρ : ℚ} (hM : 0 < M) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {v : Fin N → ℚ} (hv : v ≠ 0) (k : ℕ) :
    vR v ⬝ᵥ (Cat N 0 (cdF N M ρ v) (k + 1) - Cat N 0 (cdF N M ρ v) k)
      = gammaR N ((ρ : ℚ) : ℝ) * (reachD M v * ((qOf N ρ : ℚ) : ℝ) ^ k) := by
  have hN1 : 1 ≤ N := by omega
  have hc : cutCR (cdF N M ρ v) k = vR v := rfl
  have hsqrt := sqrtSigmaR_cdF_apply (N := N) hN1 hM hρ0 hv k
  have hdot : vR v ⬝ᵥ (((M : ℝ) * ((qOf N ρ : ℚ) : ℝ) ^ (2 * k)) • vR v)
      = (M : ℝ) * ((qOf N ρ : ℚ) : ℝ) ^ (2 * k) * (vR v ⬝ᵥ vR v) := by
    rw [dotProduct_smul, smul_eq_mul]
  rw [Cat_unfold, hc, cutPR_cdF, cdF_rho]
  unfold stepCentre
  rw [add_sub_cancel_left]
  rw [dotProduct_smul, smul_eq_mul, hdot, hsqrt]
  have hsq : reachD M v ^ 2 = (M : ℝ) * (vR v ⬝ᵥ vR v) := reachD_sq N hM hv
  have hkey : (M : ℝ) * ((qOf N ρ : ℚ) : ℝ) ^ (2 * k) * (vR v ⬝ᵥ vR v)
      = (reachD M v * ((qOf N ρ : ℚ) : ℝ) ^ k) ^ 2 := by
    rw [mul_pow, hsq]
    ring
  rw [hkey]
  have hD0 : (0 : ℝ) < reachD M v := reachD_pos N hM hv
  have hq0r : (0 : ℝ) < ((qOf N ρ : ℚ) : ℝ) := by
    have := qOf_pos hN1 hρ0
    exact_mod_cast this
  have hDq : reachD M v * ((qOf N ρ : ℚ) : ℝ) ^ k ≠ 0 := by positivity
  field_simp

/-- The initial centre is the origin: `v ⬝ Cat_0 = 0`. -/
theorem Cat_cdF_zero (N : ℕ) (M ρ : ℚ) (v : Fin N → ℚ) :
    vR v ⬝ᵥ Cat N 0 (cdF N M ρ v) 0 = 0 := by
  rw [show Cat N 0 (cdF N M ρ v) 0 = (0 : Fin N → ℝ) from rfl]
  simp [dotProduct]

/-- **THE CENTRE LAW**: along the fixed-direction stream the accumulated centre's `v`-coordinate is
exactly `D·(1 − q^k)`. -/
theorem Cat_cdF_dot (N : ℕ) (hN : 2 ≤ N) {M ρ : ℚ} (hM : 0 < M) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {v : Fin N → ℚ} (hv : v ≠ 0) :
    ∀ k, vR v ⬝ᵥ Cat N 0 (cdF N M ρ v) k
      = reachD M v * (1 - (((qOf N ρ : ℚ) : ℝ)) ^ k) := by
  intro k
  have hgam : gammaR N ((ρ : ℚ) : ℝ) = 1 - ((qOf N ρ : ℚ) : ℝ) := by
    have h1 : ((qOf N ρ : ℚ) : ℝ) = ((N : ℝ) + (ρ : ℝ)) / ((N : ℝ) + 1) := by
      rw [qOf]
      push_cast
      ring
    unfold gammaR
    rw [h1]
    have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  induction k with
  | zero => rw [Cat_cdF_zero]; simp
  | succ k ih =>
    have h := Cat_cdF_step N hN hM hρ0 hρ1 hv k
    rw [hgam] at h
    have hsplit : vR v ⬝ᵥ Cat N 0 (cdF N M ρ v) (k + 1)
        = vR v ⬝ᵥ Cat N 0 (cdF N M ρ v) k
          + vR v ⬝ᵥ (Cat N 0 (cdF N M ρ v) (k + 1) - Cat N 0 (cdF N M ρ v) k) := by
      rw [dotProduct_sub]
      ring
    rw [hsplit, ih, h, pow_succ]
    ring

#print axioms QMCLeafB.Se38M4.Cat_cdF_dot

/-! ## 4.  The reach theorem: the all-false record beyond the reach -/

/-- The shape scale of the record's initial ellipsoid. -/
def Mof (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) : ℚ :=
  2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2

/-- The contraction factor at the campaign family. -/
def qofP (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) : ℚ :=
  qOf (G.n * G.n) P.rmax

/-- The stream at the campaign's shapes. -/
def cdP (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (v : Fin (G.n * G.n) → ℚ) : ℕ → CutData (G.n * G.n) :=
  cdF (G.n * G.n) (Mof G P) P.rmax v

theorem cdP_c (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (v : Fin (G.n * G.n) → ℚ) (k : ℕ) : (cdP G P v k).c = v := rfl

theorem cdP_p (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (v : Fin (G.n * G.n) → ℚ) (k : ℕ) :
    (cdP G P v k).p = (Mof G P * (qofP G P) ^ (2 * k)) • v := rfl

theorem cdP_rho (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (v : Fin (G.n * G.n) → ℚ) (k : ℕ) : (cdP G P v k).rho = P.rmax := rfl

/-- The `v`-coordinate of the accumulated centre after `T` rounds: `D·(1 − q^T)`. -/
noncomputable def reachConst (N : ℕ) (M ρ : ℚ) (v : Fin N → ℚ) (T : ℕ) : ℝ :=
  reachD M v * (1 - (((qOf N ρ : ℚ) : ℝ)) ^ T)

/-- Along the stream the `v`-coordinate of the centre is dominated by the reach at any later round. -/
theorem Cat_cdF_le_reach (N : ℕ) (hN : 2 ≤ N) {M ρ : ℚ} (hM : 0 < M) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {v : Fin N → ℚ} (hv : v ≠ 0) {k T : ℕ} (hk : k ≤ T) :
    vR v ⬝ᵥ Cat N 0 (cdF N M ρ v) k ≤ reachConst N M ρ v T := by
  have hN1 : 1 ≤ N := by omega
  have hq0 : (0 : ℚ) < qOf N ρ := qOf_pos hN1 hρ0
  have hqr0 : (0 : ℝ) ≤ ((qOf N ρ : ℚ) : ℝ) := by exact_mod_cast le_of_lt hq0
  have hqr1 : ((qOf N ρ : ℚ) : ℝ) ≤ 1 := by
    have h := qOf_lt_one (N := N) hρ1
    exact_mod_cast le_of_lt h
  have hpow : ((qOf N ρ : ℚ) : ℝ) ^ T ≤ ((qOf N ρ : ℚ) : ℝ) ^ k :=
    pow_le_pow_of_le_one hqr0 hqr1 hk
  rw [Cat_cdF_dot N hN hM hρ0 hρ1 hv k]
  unfold reachConst
  have hD0 : (0 : ℝ) ≤ reachD M v := le_of_lt (reachD_pos N hM hv)
  nlinarith

/-- **THE REACH THEOREM.**  If the relaxation lies above a level that no accumulated centre reaches
within `K·m` rounds — in a FIXED rational direction `v` — then the all-false record EXISTS.  No
hypothesis on the programme, on the depth, or on the content of the body beyond that level. -/
theorem bodyRec_of_reach {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) (hρ1 : P.rmax < 1)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ)
    (hbody : ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P, b ≤ vR v ⬝ᵥ z)
    (hreach : reachConst (G.n * G.n) (Mof G P) P.rmax v (P.K * P.m) ≤ b) :
    QMCLeafB.ThinRec34M4.BodyRec G t P := by
  have hN : 2 ≤ G.n * G.n := by nlinarith
  have hM : (0 : ℚ) < Mof G P := by
    have := P.hdq
    unfold Mof
    positivity
  have hvpos : (0 : ℚ) < v ⬝ᵥ v := dotProduct_self_pos hv
  have hσpos : ∀ k : ℕ, (0 : ℚ) < sigmaQ v ((cdP G P v k).p) := by
    intro k
    have hq0 : (0 : ℚ) < qofP G P := by
      unfold qofP
      exact qOf_pos (by omega) P.hrmax
    have hrw : sigmaQ v ((cdP G P v k).p)
        = Mof G P * (qofP G P) ^ (2 * k) * (v ⬝ᵥ v) := by
      rw [cdP_p]
      unfold qofP
      exact sigmaQ_cdF (G.n * G.n) (Mof G P) P.rmax v k
    rw [hrw]
    have h1 : (0 : ℚ) < (qofP G P) ^ (2 * k) := pow_pos hq0 _
    have h2 : (0 : ℚ) < v ⬝ᵥ v := hvpos
    exact mul_pos (mul_pos hM h1) h2
  refine ⟨{ ok := fun _ => false
            cd := cdP G P v
            del := fun _ => 0
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
    have h := cdF_wit (G.n * G.n) hN hM P.hrmax hρ1 hv k
    exact h
  · intro k hk hok
    exact P.hrmax
  · intro k hk hok
    exact hv
  · intro k hk hok
    exact le_refl (0 : ℚ)
  · intro k hk hok
    have h := hσpos k
    have h1 : (0 : ℚ) ≤ P.rmax ^ 2 * sigmaQ (cdP G P v k).c (cdP G P v k).p :=
      mul_nonneg (sq_nonneg _) (le_of_lt h)
    simpa [cdP_c, cdP_rho] using h1
  · intro k hk hok
    exact le_refl P.rmax
  · intro k hk hok z hz
    have hz' := hbody z hz
    have hY : vR v ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (cdP G P v) k
        ≤ reachConst (G.n * G.n) (Mof G P) P.rmax v (P.K * P.m) :=
      Cat_cdF_le_reach (G.n * G.n) hN hM P.hrmax hρ1 hv (le_of_lt hk)
    have hcat : vR v ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (cdP G P v) k ≤ b :=
      le_trans hY hreach
    have hsub : vR v ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (cdP G P v) k)
        = vR v ⬝ᵥ z - vR v ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cdP G P v) k :=
      dotProduct_sub _ _ _
    rw [show cutCR (cdP G P v) k = vR v from rfl, hsub]
    push_cast
    linarith
  · show (false : Bool) = QMCLeafB.SimLoop.anyOk (fun _ => false) (P.K * P.m)
    exact (QMCLeafB.ThinRec34M4.anyOk_const_false (P.K * P.m)).symm

#print axioms QMCLeafB.Se38M4.bodyRec_of_reach

/-- The reach condition as a predicate on the point: **the body lies beyond the centre's reach in a
fixed rational direction.** -/
def ReachThin (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∃ (v : Fin (G.n * G.n) → ℚ), v ≠ 0 ∧
    (∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
      reachConst (G.n * G.n) (Mof G P) P.rmax v (P.K * P.m) ≤ vR v ⬝ᵥ z)

theorem bodyRec_of_reachThin {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) (hρ1 : P.rmax < 1)
    (H : ReachThin G t P) : QMCLeafB.ThinRec34M4.BodyRec G t P := by
  obtain ⟨v, hv, hb⟩ := H
  exact bodyRec_of_reach hn hρ1 v hv _ hb (le_refl _)

#print axioms QMCLeafB.Se38M4.bodyRec_of_reachThin

/-! ## 5.  Consequences for the leaf's slots -/

/-- **The `hfalse` slot at any bit that reads `false` there**: the record exists. -/
theorem runParts_of_reach {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (hρ1 : P.rmax < 1) (hbit : o G t = false) (H : ReachThin G t P) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o G t P) :=
  (QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec hbit).mpr
    (bodyRec_of_reachThin hn hρ1 H)

#print axioms QMCLeafB.Se38M4.runParts_of_reach

/-- The campaign's own ceiling is below one. -/
theorem rmax_P33_lt_one (G : QuantumMaxCutEnergy.Input) (hn : 1 ≤ G.n) :
    (QMCLeafB.Pbit33.P33 G).rmax < 1 := by
  show QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) < 1
  unfold QMCLeafB.RundataHalving.rmaxOf
  have hgn : (1 : ℚ) ≤ (G.n : ℚ) := by exact_mod_cast hn
  have hcast : ((G.n * G.n : ℕ) : ℚ) = (G.n : ℚ) * (G.n : ℚ) := by
    push_cast
    ring
  have h2 : (1 : ℚ) ≤ ((G.n * G.n : ℕ) : ℚ) := by
    rw [hcast]
    nlinarith
  have h3 : (0 : ℚ) < 4 * ((G.n * G.n : ℕ) : ℚ) := by linarith
  rw [div_lt_one h3]
  linarith

#print axioms QMCLeafB.Se38M4.rmax_P33_lt_one

/-- **THE COLLAR REDUCTION.**  `CollarRec` follows if every collar point is reach-thin — i.e. if at
each bit-`false`, horizon-thin, non-flat interior point the relaxation lies beyond the accumulated
centre's `K·m`-round reach in some rational direction.  This is the exact remaining quantitative
statement of the collar route: nothing about depths, ledgers or the programme. -/
theorem collarRec_of_reach
    (H : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = false → ¬ QMCLeafB.Asm36M8.Fat G t →
      ¬ QMCLeafB.Asm37M2.LevelContained G t (QMCLeafB.Pbit33.P33 G) →
      ReachThin G t (QMCLeafB.Pbit33.P33 G)) :
    QMCLeafB.Asm37M2.CollarRec := by
  intro G t hn hlo hlt hbit hfat hlc
  exact bodyRec_of_reachThin hn (rmax_P33_lt_one G (by omega)) (H G t hn hlo hlt hbit hfat hlc)

#print axioms QMCLeafB.Se38M4.collarRec_of_reach

/-- **The obstruction, in one line.**  The accumulated centre never passes the initial `v`-radius, so
the reach is at most `D`: any body served by the stream must have its `v`-support level within
`D·q^{K·m}` of the top of the initial ellipsoid. -/
theorem reachConst_le_reachD {N : ℕ} (hN : 1 ≤ N) {M ρ : ℚ} (hρ0 : 0 ≤ ρ)
    {v : Fin N → ℚ} {T : ℕ} :
    reachConst N M ρ v T ≤ reachD M v := by
  have hq0 : (0 : ℝ) ≤ ((qOf N ρ : ℚ) : ℝ) := by
    have h := qOf_pos hN hρ0
    exact_mod_cast le_of_lt h
  have hD : (0 : ℝ) ≤ reachD M v := by
    rw [reachD]
    exact Real.sqrt_nonneg _
  unfold reachConst
  nlinarith [pow_nonneg hq0 T]

#print axioms QMCLeafB.Se38M4.reachConst_le_reachD

/-- **The reach condition, in ratio form.**  `ReachThin` at a level `b` forces the `v`-support to sit
within `D·q^{K·m}` of the initial radius — i.e. the body must essentially TOUCH the initial ellipsoid
in the chosen direction.  Bodies sitting at a fixed fraction `ρ₀ < 1` of the radius (the collar's
`≈ 0.7·D`) are outside the reach at every horizon. -/
theorem reach_ratio {N : ℕ} {M ρ : ℚ} {v : Fin N → ℚ} {T : ℕ} {b : ℝ}
    (hb : reachConst N M ρ v T ≤ b) :
    reachD M v - b ≤ reachD M v * (((qOf N ρ : ℚ) : ℝ)) ^ T := by
  unfold reachConst at hb
  nlinarith

#print axioms QMCLeafB.Se38M4.reach_ratio


