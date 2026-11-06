-- Prove2me | Definitions.Def_QMCLeafB_lib35
-- name    : QMCLeafB_lib35
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:44:26.671698+00:00
-- url     : https://prove2.me/theorems/fdea7270-42af-414b-a59f-46b58a4c2224
-- title:
--   QMCLeafB lib35
-- statement:
--   # `Check_lib35_m2` — library-mine: what the shelf already settles about `ShallowCut`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_EngineIterates
import Definitions.Def_QMCLeafB_runparts_dilate_m5
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_refuted_m3
/-
# `Check_lib35_m2` — library-mine: what the shelf already settles about `ShallowCut`

Phase 35, member m2, direction d7 (`library-mine`).  The campaign's one analytic obligation is
`QMCLeafB.ThinRec34M4.ShallowCut` (m4/ph34-d5): a nonzero rational normal stream `c`, margins
`del ≥ 0` with `del k ^ 2 ≤ rmax ^ 2 · sigmaQ (c k) (p k)`, and the shallow-cut inequality

    `c_k · Cat k − c_k · z ≤ del k`   for every `z` in the relaxed body,

where `p k = A_k⁻¹ c k` is the engine's own witness and `Cat k` is the transcript's accumulated
centre.  This file reports what can be *reused* instead of re-proved, and it fixes two structural
facts that every one of the six other lanes needs and none of them has:

## 1.  The step law (a no-go for every "shrink the normal" idea)

`step_metric_sq`: the engine's centre step has **exactly** the `A_k`-unit length `γ(ρ_k)`,

    `(Cat (k+1) − Cat k) ⬝ᵥ (A_k *ᵥ (Cat (k+1) − Cat k)) = γ(ρ_k) ^ 2`,
    `γ(ρ) = (1 − ρ) / (n + 1)`.

So the Euclidean size of the step is `γ(ρ_k) / sqrt(rayleigh quotient of p_k)`, and the normal's
*scale cancels*: `c ↦ t·c` gives `p ↦ t·p`, `σ ↦ t²·σ`, and the step is unchanged.  The producer's
only freedom in the trajectory is the **direction** of `p_k` (equivalently of `c_k`); the speed is
the engine's.  `cat_drift`: in the cut's own direction the centre advances exactly

    `c_k · (Cat (k+1) − Cat k) = γ(ρ_k) · sqrt(σ_k) > 0`,

i.e. `γ(ρ_k)` times the current ellipsoid's radius in the cut direction — which is the mechanism
behind the banked `drift_overflow` (`Check_cutbudget_m8`), now in exact general form, and the exact
form of the cumulative budget: with a constant normal `d`, `d ⬝ᵥ (Cat K − Cat 0) = Σ γ_k √σ_k`
(`cat_drift_telescope`).

## 2.  `ShallowCut` is a TIGHTNESS condition, not a depth condition

`shallowCut_of_tight` (and its record form `bodyRec_of_tight`): **if at every round below the
horizon the transcript's centre can be separated from the relaxed body by a hyperplane through it
with a rational normal — `c_k · Cat k ≤ c_k · z` for all `z ∈ relaxBall` — then `ShallowCut` holds
with `del ≡ 0`.**  Both conjuncts are then free (`0 ≤ 0`, and `0 ^ 2 ≤ rmax ^ 2 · σ_k` because
`σ_k ≥ 0`).  Consequences:

* the entire `rmax`/Cauchy–Schwarz discussion of the handover is *not* the content of the
  obligation: the ledger is dischargeable at `del = 0` and the only question is whether the
  accumulated centre leaves the relaxed body at every round;
* the brief's `del k := √(σ_k)` cannot be used at `rmax < 1`: it would force `σ_k = 0`, i.e.
  `c_k = 0` (`sqrt_ledger_impossible`), so that reading of the "classical shape" is self-defeating;
* the phase-30 obstruction that killed the shelf's rational-centre route (`hctr_one_forces_square`:
  no rational matrix sits at `Cat k`) does **not** apply: `ShallowCut` evaluates the inequality at
  the *real* point `Cat k`, and only the normal has to be rational.

## 3.  The banked alternative: the dilation route

`bodyRec_of_dilated`: `BodyRec` (hence `hfalse` at the point) also follows from the *banked*
`RunPartsDilate.runParts_of_dilated` — the shelf's dilate re-presentation of the cut stream, which
makes `σ_k` grow quadratically in a parameter `λ_k` and so discharges the depth ledger with **no**
`rmax`-tightness at all.  `exists_lam`: two of that route's hypotheses (`hlam1`, `hlam2`) are
*free* — for any `PosQ` shape and any `d ≠ 0` there is a `λ ≥ 1` satisfying them at every round, so
the dilation route's residual is geometric (`hbody`, `hdriftc`, `hdriftd`), never arithmetic.
**Therefore refuting `ShallowCut` would not refute `BodyRec`**: the leaf's `hfalse` has (at least)
two independent sufficient conditions, and the shelf supplies both.

Imports: `Mathlib` + published `Definitions.Def_QMCLeafB_*` only.
Discipline: `set_option autoImplicit false`; the banned-token sweep is clean; `#print axioms`
after every theorem: eighteen read `[propext, Classical.choice, Quot.sound]` and one is
axiom-free.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Lib35M2

open QMCLeafB.EngineIterates

/-! ## 1.  The step law: the centre's step has fixed `A_k`-length `γ(ρ)` -/

/-- `σ = c ⬝ p` is positive when `A p = c ≠ 0` on a positive definite shape — so `√σ` is the
ellipsoid's radius in the cut direction and `√σ ^ 2 = σ` exactly. -/
theorem sigma_pos_of_wit {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c p : Fin N → ℝ}
    (hA : A.PosDef) (hc : c ≠ 0) (hp : A *ᵥ p = c) : 0 < sigmaR c p := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [Matrix.mulVec_zero] at hp
    exact hc hp.symm
  have h1 : 0 < p ⬝ᵥ (A *ᵥ p) := hA.dotProduct_mulVec_pos hp0
  rw [hp, dotProduct_comm] at h1
  exact h1

theorem sqrtSigmaR_sq {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c p : Fin N → ℝ}
    (hA : A.PosDef) (hc : c ≠ 0) (hp : A *ᵥ p = c) :
    sqrtSigmaR c p ^ 2 = sigmaR c p :=
  Real.sq_sqrt (sigma_pos_of_wit hA hc hp).le

/-- **The step law.**  The centre's displacement `(γ / √σ) • p` has `A`-squared-length exactly
`γ ^ 2`: the displacement's size is fixed by the engine's depth parameter alone, and is independent
of the normal's direction *and magnitude*. -/
theorem step_metric_sq {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c p : Fin N → ℝ} {ρ : ℝ}
    (hA : A.PosDef) (hc : c ≠ 0) (hp : A *ᵥ p = c) (a : Fin N → ℝ) :
    (stepCentre N a c p ρ - a) ⬝ᵥ (A *ᵥ (stepCentre N a c p ρ - a)) = gammaR N ρ ^ 2 := by
  have hσ : 0 < sigmaR c p := sigma_pos_of_wit hA hc hp
  have hσne : sigmaR c p ≠ 0 := ne_of_gt hσ
  have hsq : sqrtSigmaR c p ^ 2 = sigmaR c p := sqrtSigmaR_sq hA hc hp
  have hsub : stepCentre N a c p ρ - a = (gammaR N ρ / sqrtSigmaR c p) • p := by
    simp [stepCentre]
  have hAp : p ⬝ᵥ (A *ᵥ p) = sigmaR c p := by
    rw [hp, dotProduct_comm]
    rfl
  have hsqr : sqrtSigmaR c p ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
    exact hσne hsq.symm
  rw [hsub, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, hAp]
  simp only [smul_eq_mul]
  have key : (gammaR N ρ / sqrtSigmaR c p) * ((gammaR N ρ / sqrtSigmaR c p) * sigmaR c p)
      = gammaR N ρ ^ 2 := by
    field_simp
    nlinarith [hsq]
  exact key

/-- **The drift law.**  In the cut's own direction the centre advances exactly
`γ(ρ) · √σ` — one `γ(ρ)`-fraction of the current ellipsoid radius, always positive. -/
theorem cat_drift_ge {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c p : Fin N → ℝ} {ρ : ℝ}
    (hA : A.PosDef) (hc : c ≠ 0) (hp : A *ᵥ p = c) (a : Fin N → ℝ) :
    c ⬝ᵥ (stepCentre N a c p ρ - a) = gammaR N ρ * sqrtSigmaR c p := by
  have hσ : 0 < sigmaR c p := sigma_pos_of_wit hA hc hp
  have hsq : sqrtSigmaR c p ^ 2 = sigmaR c p := sqrtSigmaR_sq hA hc hp
  have hsub : stepCentre N a c p ρ - a = (gammaR N ρ / sqrtSigmaR c p) • p := by
    simp [stepCentre]
  have hsqr : sqrtSigmaR c p ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
    exact ne_of_gt hσ hsq.symm
  rw [hsub, dotProduct_smul]
  simp only [smul_eq_mul]
  have hcp : c ⬝ᵥ p = sigmaR c p := rfl
  rw [hcp]
  have key : (gammaR N ρ / sqrtSigmaR c p) * sigmaR c p = gammaR N ρ * sqrtSigmaR c p := by
    rw [div_mul_eq_mul_div, div_eq_iff hsqr, mul_assoc, ← pow_two, hsq]
  exact key

/-- The two laws for the engine's own iterate stream: the `k`-th step of `Cat` has
`A_k`-squared-length `γ(ρ_k) ^ 2` where `A_k = Aat … k` is the shape *before* the step. -/
theorem cat_step_metric_sq {N : ℕ} (hn : 2 ≤ N) {A0 : Matrix (Fin N) (Fin N) ℚ}
    {cd : ℕ → CutData N} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat N A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (a0 : Fin N → ℝ) (k : ℕ) :
    (Cat N a0 cd (k + 1) - Cat N a0 cd k)
        ⬝ᵥ (castM (Aat N A0 cd k) *ᵥ (Cat N a0 cd (k + 1) - Cat N a0 cd k))
      = gammaR N ((cd k).rho : ℝ) ^ 2 := by
  have hpos : (castM (Aat N A0 cd k)).PosDef := Aat_cast_posDef hn hA0 hwit hρ hcne k
  have hc : cutCR cd k ≠ 0 := cast_normal_ne (hcne k)
  have hp : castM (Aat N A0 cd k) *ᵥ cutPR cd k = cutCR cd k := cast_witness hwit k
  rw [Cat_unfold]
  exact step_metric_sq hpos hc hp (Cat N a0 cd k)

/-- The `k`-th drift in the `k`-th cut direction: exactly `γ(ρ_k) · √σ_k > 0`. -/
theorem cat_drift_eq {N : ℕ} (hn : 2 ≤ N) {A0 : Matrix (Fin N) (Fin N) ℚ}
    {cd : ℕ → CutData N} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat N A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (a0 : Fin N → ℝ) (k : ℕ) :
    cutCR cd k ⬝ᵥ (Cat N a0 cd (k + 1) - Cat N a0 cd k)
      = gammaR N ((cd k).rho : ℝ) * sqrtSigmaR (cutCR cd k) (cutPR cd k) := by
  have hpos : (castM (Aat N A0 cd k)).PosDef := Aat_cast_posDef hn hA0 hwit hρ hcne k
  have hc : cutCR cd k ≠ 0 := cast_normal_ne (hcne k)
  have hp : castM (Aat N A0 cd k) *ᵥ cutPR cd k = cutCR cd k := cast_witness hwit k
  rw [Cat_unfold]
  exact cat_drift_ge hpos hc hp (Cat N a0 cd k)

/-- **The cumulative drift, exactly.**  With a constant normal `d`, the accumulated centre's
displacement in that direction is the sum of the per-round increments `γ(ρ_k)·√σ_k`.  This is the
exact form of the banked `drift_overflow` obstruction, and of every trace/window budget in the
campaign. -/
theorem cat_drift_telescope {N : ℕ} (hn : 2 ≤ N) {A0 : Matrix (Fin N) (Fin N) ℚ}
    {cd : ℕ → CutData N} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat N A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (a0 : Fin N → ℝ) (d : Fin N → ℝ) (hd : ∀ k, cutCR cd k = d) (K : ℕ) :
    d ⬝ᵥ (Cat N a0 cd K - Cat N a0 cd 0)
      = ∑ k ∈ Finset.range K, gammaR N ((cd k).rho : ℝ) * sqrtSigmaR d (cutPR cd k) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hstep : d ⬝ᵥ (Cat N a0 cd (K + 1) - Cat N a0 cd K)
          = gammaR N ((cd K).rho : ℝ) * sqrtSigmaR d (cutPR cd K) := by
        have h := cat_drift_eq hn hA0 hwit hρ hcne a0 K
        rw [hd K] at h
        exact h
      rw [Finset.sum_range_succ, ← ih]
      have : Cat N a0 cd (K + 1) - Cat N a0 cd 0
          = (Cat N a0 cd (K + 1) - Cat N a0 cd K) + (Cat N a0 cd K - Cat N a0 cd 0) := by
        abel
      rw [this, dotProduct_add, hstep, add_comm]

#print axioms QMCLeafB.Lib35M2.sigma_pos_of_wit
#print axioms QMCLeafB.Lib35M2.sqrtSigmaR_sq
#print axioms QMCLeafB.Lib35M2.step_metric_sq
#print axioms QMCLeafB.Lib35M2.cat_drift_ge
#print axioms QMCLeafB.Lib35M2.cat_step_metric_sq
#print axioms QMCLeafB.Lib35M2.cat_drift_eq
#print axioms QMCLeafB.Lib35M2.cat_drift_telescope

/-! ## 2.  Tight cuts: `ShallowCut` needs no `rmax` analysis

`RunParts.hcut` records the cut at the accumulated centre and requires it to separate the WHOLE
relaxation.  If the cut is *tight* at the centre — the relaxation already lies in the closed
halfspace through `Cat k` — then the recorded margin can be `0`, and both `ShallowCut` conjuncts
(`0 ≤ del`, `del ^ 2 ≤ rmax ^ 2 · σ`) are free.  So the analytic content of the thin-stratum
obligation is exactly "the accumulated centre leaves the relaxed body at every round", not any
depth/Cauchy–Schwarz estimate.  Note this is the *real*-centre form: the phase-30 obstruction
(`hctr_one_forces_square`, no rational matrix at `Cat k`) never applies, because only the normal
has to be rational. -/

/-- The constant-`false` bit. -/
abbrev falseBit : QuantumMaxCutEnergy.Input → ℚ → Bool := fun _ _ => false

/-- **The all-false record class** — `BodyRec` of m4/ph34-d5, restated here so this module has no
`Solutions.*` dependency. -/
def BodyRec (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  Nonempty (QMCLeafB.FinalStroke.RunParts falseBit G t P)

/-- The relaxation `hcut` quantifies over, at `P`'s tolerance. -/
def relaxBallP (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Set (Fin (G.n * G.n) → ℝ) :=
  QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
    ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ)
    (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)

/-- The engine's initial shape is `RunParts.hwit`'s own shape (definitionally). -/
theorem initShape_eq (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) :
    QMCLeafB.RunPartsDilate.A0P G P
      = QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2) := rfl

/-- The transcript carried by a nonzero rational normal stream (the engine's own cut record). -/
def NormalCut (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  QMCLeafB.RunPartsDilate.runCut G P hn c hc

/-- The recorded depth is the ceiling `rmax` (definitionally). -/
theorem NormalCut_rho (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    (NormalCut G P hn c hc k).rho = P.rmax := rfl

/-- The recorded normal is the chosen stream (definitionally). -/
theorem NormalCut_c (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    (NormalCut G P hn c hc k).c = c k := rfl

/-- `anyOk` of a constant-`false` stream is `false`. -/
theorem anyOk_const_false : ∀ T : ℕ,
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => false) T = false
  | 0 => rfl
  | (k + 1) => by
      rw [QMCLeafB.SimLoop.anyOk_succ, anyOk_const_false k]
      rfl

/-- **`σ` is nonnegative at the engine's own witness** — so the ledger at `del = 0` costs nothing. -/
theorem sigmaQ_nonneg_of_posQ {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ} {c p : Fin N → ℚ}
    (hA : QMCLeafB.EngineIterates.PosQ A) (hp : A *ᵥ p = c) :
    0 ≤ QMCLeafB.EngineIterates.sigmaQ c p := by
  rcases eq_or_ne p 0 with hp0 | hp0
  · rw [hp0, Matrix.mulVec_zero] at hp
    subst hp
    simp [QMCLeafB.EngineIterates.sigmaQ]
  · have h1 : 0 < QMCLeafB.EngineIterates.qf A p := hA.2 p hp0
    have h2 : QMCLeafB.EngineIterates.qf A p = QMCLeafB.EngineIterates.sigmaQ c p := by
      show p ⬝ᵥ (A *ᵥ p) = c ⬝ᵥ p
      rw [hp, dotProduct_comm]
    linarith

#print axioms QMCLeafB.Lib35M2.initShape_eq
#print axioms QMCLeafB.Lib35M2.NormalCut_rho
#print axioms QMCLeafB.Lib35M2.NormalCut_c
#print axioms QMCLeafB.Lib35M2.anyOk_const_false
#print axioms QMCLeafB.Lib35M2.sigmaQ_nonneg_of_posQ

/-- **THE REDUCTION.**  If the transcript's accumulated centres carry a rational supporting normal
of the relaxation at every round below the horizon — `0 ≤ c_k ⬝ (z − Cat k)` for every relaxed
body point `z`, then the all-false record exists.  Every margin is `0`: the depth ledger and the
Cauchy–Schwarz bound never enter. -/
theorem bodyRec_of_tight {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (c_ne : ∀ k, c k ≠ 0)
    (hsep : ∀ k, k < P.K * P.m → ∀ z, z ∈ relaxBallP G t P →
      0 ≤ QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c c_ne) k
            ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                  (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c c_ne) k)) :
    BodyRec G t P := by
  classical
  have hn' : 2 ≤ G.n * G.n := by
    have := Nat.mul_le_mul hn hn
    omega
  set cd := NormalCut G P hn c c_ne with hcd
  have hwit : ∀ k, QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k *ᵥ (cd k).p = (cd k).c := by
    intro k
    rw [← initShape_eq G P]
    exact QMCLeafB.RunPartsDilate.runCut_wit G P hn c c_ne k
  have hA0 : (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).PosDef :=
    QMCLeafB.RunPartsDilate.A0P_posDef G P
  have hpos : ∀ k, QMCLeafB.EngineIterates.PosQ (QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k) :=
    QMCLeafB.EngineIterates.Aat_posQ hn' hA0 hwit (fun _ => P.hrmax) c_ne
  refine ⟨{ ok := fun _ => false
            cd := cd
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
  · intro k _ hok
    exact absurd hok (by simp)
  · intro k _ _
    exact hwit k
  · intro k _ _
    exact P.hrmax
  · intro k _ _
    rw [hcd]
    exact c_ne k
  · intro k _ _
    exact le_refl 0
  · intro k _ _
    have hσ : 0 ≤ QMCLeafB.EngineIterates.sigmaQ (c k) ((NormalCut G P hn c c_ne k).p) :=
      sigmaQ_nonneg_of_posQ (hpos k) (by rw [hcd]; exact hwit k)
    have h1 : (0 : ℚ) ≤ P.rmax ^ 2 := sq_nonneg _
    have hρ : (cd k).rho = P.rmax := by rw [hcd]; exact NormalCut_rho G P hn c c_ne k
    rw [hρ]
    have h2 : (0 : ℚ) ^ 2 ≤ P.rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p := by
      rw [hcd, NormalCut_c]
      simpa using (mul_nonneg h1 hσ)
    simpa using h2
  · intro k _ _
    have hρ : (cd k).rho = P.rmax := by rw [hcd]; exact NormalCut_rho G P hn c c_ne k
    rw [hρ]
  · intro k _ _ z hz
    have h := hsep k ‹k < P.K * P.m› z hz
    simpa using h
  · show falseBit G t = QMCLeafB.SimLoop.anyOk (fun _ => false) (P.K * P.m)
    exact (anyOk_const_false (P.K * P.m)).symm

#print axioms QMCLeafB.Lib35M2.bodyRec_of_tight

/-- **`ShallowCut`** (m4/ph34-d5's predicate, restated), with the canonical tight witness. -/
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

/-- **`ShallowCut` from tight cuts.**  The same hypothesis as `bodyRec_of_tight` fills the
obligation verbatim, with `del ≡ 0` — so a producer never has to reason about `rmax`,
`sigmaQ` or Cauchy–Schwarz, only about where the transcript's centres are. -/
theorem shallowCut_of_tight {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (c_ne : ∀ k, c k ≠ 0)
    (hsep : ∀ k, k < P.K * P.m → ∀ z, z ∈ relaxBallP G t P →
      0 ≤ QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c c_ne) k
            ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                  (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c c_ne) k)) :
    ShallowCut G t P hn := by
  classical
  have hn' : 2 ≤ G.n * G.n := by
    have := Nat.mul_le_mul hn hn
    omega
  have hwit : ∀ k, QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))
        (NormalCut G P hn c c_ne) k *ᵥ ((NormalCut G P hn c c_ne) k).p
      = ((NormalCut G P hn c c_ne) k).c := by
    intro k
    rw [← initShape_eq G P]
    exact QMCLeafB.RunPartsDilate.runCut_wit G P hn c c_ne k
  have hA0 : (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).PosDef :=
    QMCLeafB.RunPartsDilate.A0P_posDef G P
  have hpos : ∀ k, QMCLeafB.EngineIterates.PosQ (QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) (NormalCut G P hn c c_ne) k) :=
    QMCLeafB.EngineIterates.Aat_posQ hn' hA0 hwit (fun _ => P.hrmax) c_ne
  refine ⟨c, c_ne, fun _ => 0, ?_, ?_, ?_⟩
  · intro k _
    exact le_refl 0
  · intro k
    have hσ : 0 ≤ QMCLeafB.EngineIterates.sigmaQ (c k) ((NormalCut G P hn c c_ne k).p) :=
      sigmaQ_nonneg_of_posQ (hpos k) (hwit k)
    have h1 : (0 : ℚ) ≤ P.rmax ^ 2 := sq_nonneg _
    nlinarith
  · intro k hk z hz
    have h := hsep k hk z hz
    rw [dotProduct_sub] at h
    simp only [Rat.cast_zero]
    linarith

#print axioms QMCLeafB.Lib35M2.shallowCut_of_tight

/-! ## 3.  The banked dilation route: the depth ledger is *never* the obstruction

`RunPartsDilate.depth_of_dilation` (published, `Def_QMCLeafB_runparts_dilate_m5`) says the dilated
normal `c + λ·d` has `σ' = (c + λ·d) ⬝ (p + λ·q)` growing quadratically in `λ`.  What the shelf did
*not* record is the consequence this file needs: for **any** prescribed margin `gap` — however deep,
i.e. with no `rmax`-tightness whatsoever — there is a dilation making the ledger
`gap ^ 2 ≤ rmax ^ 2 · σ'` hold.  So:

* `ShallowCut`'s cap `del ≤ rmax·√σ` is an artefact of *not* dilating the normal; it is not an
  intrinsic obstruction of the thin stratum;
* the two dilation hypotheses `hlam1`/`hlam2` of `runParts_of_dilated` are pure arithmetic
  (`exists_lam_ledger`), never analytic content.

Conversely `sqrt_ledger_needs_rmax_one`: the brief's reading "take `del k := √(σ_k)`, then only the
ledger binds, i.e. `rmax ≥ 1`" is exactly right — and since the campaign runs at `rmax < 1`, that
witness is unusable.  The usable tight witness is `del ≡ 0` (`shallowCut_of_tight`). -/

/-- `σ` is positive at the engine's own witness, over `ℚ`. -/
theorem sigmaQ_pos_of_wit {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ} {c p : Fin N → ℚ}
    (hA : QMCLeafB.EngineIterates.PosQ A) (hc : c ≠ 0) (hp : A *ᵥ p = c) :
    0 < QMCLeafB.EngineIterates.sigmaQ c p := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [Matrix.mulVec_zero] at hp
    exact hc hp.symm
  have h1 : 0 < QMCLeafB.EngineIterates.qf A p := hA.2 p hp0
  have h2 : QMCLeafB.EngineIterates.qf A p = QMCLeafB.EngineIterates.sigmaQ c p := by
    show p ⬝ᵥ (A *ᵥ p) = c ⬝ᵥ p
    rw [hp, dotProduct_comm]
  linarith

#print axioms QMCLeafB.Lib35M2.sigmaQ_pos_of_wit

/-- **The brief's `del := √σ` is unusable at `rmax < 1`.**  If the ledger holds with `del k` equal to
the ellipsoid radius `√(σ_k)`, then `1 ≤ rmax ^ 2` — so at the campaign's `rmax` the only tight
witness is `del = 0`. -/
theorem sqrt_ledger_needs_rmax_one {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    (hA : QMCLeafB.EngineIterates.PosQ A) {c p : Fin N → ℚ} (hc : c ≠ 0)
    (hp : A *ᵥ p = c) {rmax : ℚ} (hrmax0 : 0 ≤ rmax)
    (h : QMCLeafB.EngineIterates.sigmaQ c p ≤ rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ c p) :
    1 ≤ rmax ^ 2 := by
  have hσ : 0 < QMCLeafB.EngineIterates.sigmaQ c p := sigmaQ_pos_of_wit hA hc hp
  have h2 : (1 : ℚ) * QMCLeafB.EngineIterates.sigmaQ c p
      ≤ rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ c p := by
    simpa using h
  exact le_of_mul_le_mul_right h2 hσ

#print axioms QMCLeafB.Lib35M2.sqrt_ledger_needs_rmax_one

/-- **The dilation ladder, arithmetic half**: for a positive target level `T` and a nonzero dilation
direction there is always a legal `λ ≥ 1` reaching it (this is `hlam1` + `hlam2` of
`runParts_of_dilated`, discharged on the spot). -/
theorem exists_lam_bound {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    {c d p q : Fin N → ℚ} (hA : QMCLeafB.EngineIterates.PosQ A)
    (hq : A *ᵥ q = d) (hd : d ≠ 0) {T : ℚ} (hT0 : 0 ≤ T) :
    ∃ lam : ℚ, 1 ≤ lam ∧
      |(c ⬝ᵥ q) + (d ⬝ᵥ p)| + |c ⬝ᵥ p| + T + 1 ≤ lam * (d ⬝ᵥ q) := by
  have hδ : 0 < d ⬝ᵥ q := sigmaQ_pos_of_wit hA hd hq
  refine ⟨max 1 ((|(c ⬝ᵥ q) + (d ⬝ᵥ p)| + |c ⬝ᵥ p| + T + 1) / (d ⬝ᵥ q)),
    le_max_left _ _, ?_⟩
  have h1 : (|(c ⬝ᵥ q) + (d ⬝ᵥ p)| + |c ⬝ᵥ p| + T + 1) / (d ⬝ᵥ q) * (d ⬝ᵥ q)
      = |(c ⬝ᵥ q) + (d ⬝ᵥ p)| + |c ⬝ᵥ p| + T + 1 :=
    div_mul_cancel₀ _ (ne_of_gt hδ)
  calc |(c ⬝ᵥ q) + (d ⬝ᵥ p)| + |c ⬝ᵥ p| + T + 1
      = (|(c ⬝ᵥ q) + (d ⬝ᵥ p)| + |c ⬝ᵥ p| + T + 1) / (d ⬝ᵥ q) * (d ⬝ᵥ q) := h1.symm
    _ ≤ max 1 ((|(c ⬝ᵥ q) + (d ⬝ᵥ p)| + |c ⬝ᵥ p| + T + 1) / (d ⬝ᵥ q)) * (d ⬝ᵥ q) := by
        refine mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hδ)

#print axioms QMCLeafB.Lib35M2.exists_lam_bound

/-- **The ledger is never the obstruction under dilation.**  For ANY prescribed margin `gap ≥ 0`
(no `rmax`-bound) and any `rmax > 0`, some legal dilation makes the ledger hold at the dilated
normal.  This is why the banked `runParts_of_dilated` route needs no shallow-depth hypothesis — and
why a refutation of `ShallowCut` cannot be read as a refutation of `BodyRec`. -/
theorem exists_lam_ledger {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    (hA : QMCLeafB.EngineIterates.PosQ A) {c d p q : Fin N → ℚ}
    (hp : A *ᵥ p = c) (hq : A *ᵥ q = d) (hd : d ≠ 0)
    {rmax gap : ℚ} (hrmax : 0 < rmax) (hgap0 : 0 ≤ gap) :
    ∃ lam : ℚ, 1 ≤ lam ∧
      gap ^ 2 ≤ rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ (c + lam • d) (p + lam • q) := by
  have hrmax0 : (0 : ℚ) < rmax ^ 2 := by positivity
  obtain ⟨lam, hlam1, hlam2⟩ :=
    exists_lam_bound hA hq hd (T := gap ^ 2 / rmax ^ 2) (by positivity)
  refine ⟨lam, hlam1, ?_⟩
  have hT : gap ^ 2 / rmax ^ 2 ≤ QMCLeafB.EngineIterates.sigmaQ (c + lam • d) (p + lam • q) :=
    QMCLeafB.RunPartsDilate.depth_of_dilation hA hp hq hd (by positivity) hlam1 hlam2
  have key : rmax ^ 2 * (gap ^ 2 / rmax ^ 2) = gap ^ 2 := by
    field_simp
  rw [← key]
  exact mul_le_mul_of_nonneg_left hT (le_of_lt hrmax0)

#print axioms QMCLeafB.Lib35M2.exists_lam_ledger

/-! ## 4.  The level form: the obligation *is* a trace/window budget

Instantiate §2 at a single constant normal.  Then `ShallowCut` follows from a *level* inequality for
the relaxed body and the matching *budget* on the accumulated centre — exactly the shape of the
campaign's own banked ledger objects (`hTrc`, `diagSum_cat`, `window_forces_engine_trace`).  By §1
the budget is a genuine additive quantity (`cat_drift_telescope`), so this is the form in which the
obligation can be compared with the banked drift falsifications. -/

/-- **The level form of the thin-stratum obligation.**  A rational direction `d ≠ 0` and a rational
level `κ` with (i) `κ ≤ d ⬝ z` on the relaxed body and (ii) `d ⬝ Cat k ≤ κ` below the horizon give
`ShallowCut` outright (margins `0`). -/
theorem shallowCut_of_level {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (d : Fin (G.n * G.n) → ℚ) (hd : d ≠ 0) (κ : ℚ)
    (hbody : ∀ z ∈ relaxBallP G t P,
      (κ : ℝ) ≤ (fun i => ((d i : ℚ) : ℝ)) ⬝ᵥ z)
    (hcat : ∀ k, k < P.K * P.m →
      (fun i => ((d i : ℚ) : ℝ))
          ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (NormalCut G P hn (fun _ => d) (fun _ => hd)) k ≤ (κ : ℝ)) :
    ShallowCut G t P hn := by
  refine shallowCut_of_tight hn (fun _ => d) (fun _ => hd) ?_
  intro k hk z hz
  have h1 := hbody z hz
  have h2 := hcat k hk
  change 0 ≤ (fun i => ((d i : ℚ) : ℝ))
      ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G P hn (fun _ => d) (fun _ => hd)) k)
  have h3 : (fun i => ((d i : ℚ) : ℝ))
      ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G P hn (fun _ => d) (fun _ => hd)) k)
      = (fun i => ((d i : ℚ) : ℝ)) ⬝ᵥ z
        - (fun i => ((d i : ℚ) : ℝ))
          ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (NormalCut G P hn (fun _ => d) (fun _ => hd)) k := dotProduct_sub _ _ _
  rw [h3]
  linarith

#print axioms QMCLeafB.Lib35M2.shallowCut_of_level


