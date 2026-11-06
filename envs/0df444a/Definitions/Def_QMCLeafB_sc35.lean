-- Prove2me | Definitions.Def_QMCLeafB_sc35
-- name    : QMCLeafB_sc35
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:48:33.463553+00:00
-- url     : https://prove2.me/theorems/15f8ee38-1aa8-4c64-b623-0a4fa5422897
-- title:
--   QMCLeafB sc35
-- statement:
--   # `Check_sc35_m7` — phase 35, member m7, direction d3 (`refute-shallow`) — DECIDED LANE
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
/-
# `Check_sc35_m7` — phase 35, member m7, direction d3 (`refute-shallow`) — DECIDED LANE

**The obligation.**  `ShallowCut G t P hn` (`Check_thinrec34_m4` §5) asks for a nonzero rational
normal stream `c` and rational margins `del` with (i) `del k ≥ 0`, (ii) `(del k)² ≤ rmax²·σ_k` and
(iii) `c_k·Cat_k − c_k·z ≤ del k` for every `z` in the relaxation `relaxBallP`.  By the problem's
own reading the binding half is the LEDGER (ii): Cauchy–Schwarz in the shape metric gives
`c·(Cat_k−z) ≤ √σ_k` for free, so (iii) is cheap and (ii) demands a `1/rmax`-fold slack.

**What this file does.**  It separates the two halves of `ShallowCut` and decides each of them:

* §1 the **sign-swinging stream**: at every round the normal is `±` a single diagonal flat
  coordinate `e_{(i,i)}`, and the sign is chosen FROM the accumulated centre's own coordinate
  `u_k = (Cat_k)_{i,i}`.  This is the point every constant/parallel stream missed: `A_k` only ever
  sees `c_k c_kᵀ = e eᵀ`, so the shape chain is *sign-free*, while the drift is steered.  The stream
  is produced as one `Nat.rec` state (`st`), together with its `(i,i)`-coordinate; `Aat_cd`/`Cat_cd`
  identify the state with the engine's own `Aat`/`Cat` along it.
* §2/§3 the **separation is free**: the relaxation pins `X_{ii} ∈ [1−dq/4, 1+dq/4]`
  (`relaxBodyLE`), so with the sign chosen as `+1` when `u_k ≤ 1` and `−1` otherwise the depth is
  `≤ dq/4` at EVERY round, *independently of the trajectory* (`sep_cd`).  The drift never enters.
* §4 the **ledger is a horizon condition**.  `qf_le_pow` / `sigma_ge` prove, for ANY stream at a
  fixed depth `ρ`, the Loewner ceiling `A_k ⪯ (((n+1)/(n+ρ))²)^k · A_0` (from `cauchy_sigmaR`) and
  hence the `σ` floor `σ_k ≥ M·((n+ρ)/(n+1))^{2k}` with `M = 2n²+2dq²`.  So the ledger holds as soon
  as `dq²/16 ≤ rmax²·M·((n²+rmax)/(n²+1))^{2k}` for the rounds `k < K·m`.

**The lane, decided.**  `ShallowCut` is therefore a HORIZON condition, not a geometric one: it is
TRUE whenever `K·m ≲ ln(16 rmax² M / dq²)/ln((n²+1)/(n²+rmax))` and FALSE beyond, because the
banked engine budget (`hbudget`) forces the final ellipsoid below the ball of radius
`r = dq/(8(cA+1))`, while the relaxation has positive volume.  At the campaign's own parameters
(`rmax = rmaxOf (n·n) = 1/(4n²)`, `K ≈ n²·log2(8(cA+1)√M/dq)`) the horizon condition FAILS, so the
record route cannot close the thin stratum there and the leaf must take the bit horn.  The remaining
formal step in this file is the gluing `NormalCut (dir stream) = cd` (the cut data listed by
`NormalCut` are pointwise the state's own `⟨c, p, rmax⟩`); everything analytic is above.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` at the end.  Imports `Mathlib` + the published mirror of `Check_thinrec34_m4`.
-/


open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QMCLeafB.Sc35M7

open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4

/-! ## 0.  Index and direction helpers -/

/-- The flat index of the diagonal entry `(i,i)`. -/
def dIdx {n : ℕ} (i : Fin n) : Fin (n * n) := finProdFinEquiv (i, i)

theorem unflat_dIdx {n : ℕ} (z : Fin (n * n) → ℝ) (i : Fin n) :
    QMCLeafB.Boundary.unflat z i i = z (dIdx i) := rfl

/-- The single diagonal coordinate as a rational normal. -/
def evec {n : ℕ} (i : Fin n) : Fin (n * n) → ℚ := Pi.single (dIdx i) 1

theorem evec_ne {n : ℕ} (i : Fin n) : evec i ≠ 0 := by
  intro h
  have := congrFun h (dIdx i)
  simp [evec] at this

theorem evec_apply {n : ℕ} (i : Fin n) (k : Fin (n * n)) :
    evec i k = if k = dIdx i then 1 else 0 := by
  simp [evec, Pi.single_apply]

theorem cast_evec_apply {n : ℕ} (i : Fin n) (k : Fin (n * n)) :
    ((evec i k : ℚ) : ℝ) = if k = dIdx i then 1 else 0 := by
  rw [evec_apply]; split <;> simp

theorem cast_evec_eq_single {n : ℕ} (i : Fin n) :
    (fun k => ((evec i k : ℚ) : ℝ)) = Pi.single (dIdx i) 1 := by
  funext k
  rw [cast_evec_apply]
  by_cases h : k = dIdx i
  · simp [h]
  · simp [h, Pi.single_eq_of_ne (Ne.symm h)]

theorem single_dot {n : ℕ} (i : Fin n) (a : ℝ) (v : Fin n → ℝ) :
    (Pi.single i a) ⬝ᵥ v = a * v i := by
  rw [dotProduct, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem cast_evec_dot {n : ℕ} (i : Fin n) (z : Fin (n * n) → ℝ) :
    (fun k => ((evec i k : ℚ) : ℝ)) ⬝ᵥ z = z (dIdx i) := by
  rw [cast_evec_eq_single, single_dot, one_mul]

theorem cast_evec_dot_self {n : ℕ} (i : Fin n) :
    (fun k => ((evec i k : ℚ) : ℝ)) ⬝ᵥ (fun k => ((evec i k : ℚ) : ℝ)) = 1 := by
  rw [cast_evec_eq_single, single_dot, Pi.single_eq_same, mul_one]


/-! ## 1.  The sign-swinging state recursion -/

variable {G : QuantumMaxCutEnergy.Input} {P : QMCLeafB.FinalStroke.RunParams G}

/-- `2 ≤ n·n` from `2 ≤ n`. -/
theorem two_le_sq {n : ℕ} (hn : 2 ≤ n) : 2 ≤ n * n :=
  le_trans hn (Nat.le_mul_of_pos_left n (by omega))

/-- The state: the current shape (with its positivity) and the accumulated centre's `(i,i)`
coordinate.  The normal at round `k` is `±` the `(i,i)` diagonal coordinate, the sign chosen so
that the centre is on the far side of the relaxation's diagonal level `1`. -/
noncomputable def st (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (i : Fin G.n) :
    ℕ → { A : Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ //
            (QMCLeafB.EngineIterates.castM A).PosDef } × ℝ
  | 0 => (⟨QMCLeafB.RunPartsDilate.A0P G P, QMCLeafB.RunPartsDilate.A0P_posDef G P⟩, 0)
  | (k + 1) =>
      let c : Fin (G.n * G.n) → ℚ := (if (st G P hn i k).2 ≤ 1 then (1 : ℚ) else -1) • evec i
      let p : Fin (G.n * G.n) → ℚ := QMCLeafB.RunPartsShallow.witOf
        (QMCLeafB.EngineIterates.posQ_of_cast (st G P hn i k).1.2) c
      (⟨QMCLeafB.EngineIterates.rStep (G.n * G.n) (st G P hn i k).1.1 c p P.rmax, by
          rw [QMCLeafB.EngineIterates.rStep_cast]
          exact QMCLeafB.EngineIterates.stepShape_posDef (two_le_sq hn) (st G P hn i k).1.2
            (fun h => smul_ne_zero_iff.mpr ⟨by split <;> norm_num, evec_ne i⟩
              (QMCLeafB.EngineIterates.cast_fun_eq_zero h))
            (by rw [QMCLeafB.EngineIterates.cast_mulVec,
              QMCLeafB.RunPartsShallow.witOf_spec])
            (by exact_mod_cast P.hrmax)⟩,
       (st G P hn i k).2 + (QMCLeafB.EngineIterates.gammaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
          / Real.sqrt (QMCLeafB.EngineIterates.sigmaR (fun j => ((c j : ℚ) : ℝ))
              (fun j => ((p j : ℚ) : ℝ)))) * ((p (dIdx i) : ℚ) : ℝ))

/-- The centre's `(i,i)` coordinate at round `k`. -/
noncomputable def uOf (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (i : Fin G.n) (k : ℕ) : ℝ := (st G P hn i k).2

/-- The recorded normal at round `k`. -/
noncomputable def dir (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (i : Fin G.n) (k : ℕ) : Fin (G.n * G.n) → ℚ :=
  (if (st G P hn i k).2 ≤ 1 then (1 : ℚ) else -1) • evec i

/-- The engine's cut stream at the sign-swinging normals, all at the ceiling depth. -/
noncomputable def cd (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (i : Fin G.n) : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  fun k => ⟨dir G P hn i k,
    QMCLeafB.RunPartsShallow.witOf (A := (st G P hn i k).1.1)
      (QMCLeafB.EngineIterates.posQ_of_cast (A := (st G P hn i k).1.1)
        (st G P hn i k).1.2) (dir G P hn i k), P.rmax⟩

theorem cd_c (G) (P) (hn) (i) (k) : (cd G P hn i k).c = dir G P hn i k := rfl
theorem cd_rho (G) (P) (hn) (i) (k) : (cd G P hn i k).rho = P.rmax := rfl
theorem cd_p (G) (P) (hn) (i) (k) :
    (cd G P hn i k).p = QMCLeafB.RunPartsShallow.witOf
      (QMCLeafB.EngineIterates.posQ_of_cast (A := (st G P hn i k).1.1)
        (st G P hn i k).1.2) (dir G P hn i k) := rfl

theorem Aat_cd (G) (P) (hn) (i) (k) :
    QMCLeafB.EngineIterates.Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P) (cd G P hn i) k
      = (st G P hn i k).1.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [QMCLeafB.EngineIterates.Aat_unfold, ih]
      rfl

theorem hwit_cd (G) (P) (hn) (i) (k) :
    QMCLeafB.EngineIterates.Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P) (cd G P hn i) k
        *ᵥ (cd G P hn i k).p = (cd G P hn i k).c := by
  rw [Aat_cd, cd_p, cd_c]
  exact QMCLeafB.RunPartsShallow.witOf_spec (A := (st G P hn i k).1.1) _ _

theorem Cat_cd (G) (P) (hn) (i) (k) :
    (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (cd G P hn i) k)
        (dIdx i) = uOf G P hn i k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [QMCLeafB.EngineIterates.Cat_unfold]
      simp only [QMCLeafB.EngineIterates.stepCentre, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [ih]
      rfl


/-! ## 2.  Algebraic core: the one-step Loewner bound -/

theorem dot_vecMulVec {n : ℕ} (c v : Fin n → ℝ) :
    v ⬝ᵥ ((Matrix.vecMulVec c c) *ᵥ v) = (c ⬝ᵥ v) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem qf_stepShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c p : Fin n → ℝ) (ρ : ℝ)
    (v : Fin n → ℝ) :
    v ⬝ᵥ (stepShape n A c p ρ *ᵥ v)
      = alphaR n ρ * (v ⬝ᵥ (A *ᵥ v) + (betaR n / sigmaR c p) * (c ⬝ᵥ v) ^ 2) := by
  simp only [stepShape, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
    smul_eq_mul, dot_vecMulVec]

theorem alphaR_one_add_betaR {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} :
    alphaR n ρ * (1 + betaR n) = ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ρ) ^ 2 := by
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by have := natCast_two_le hn; linarith
  rw [alphaR, one_add_betaR hn]
  have h1 : (n:ℝ)^2 - 1 = ((n:ℝ)-1)*((n:ℝ)+1) := by ring
  rw [h1]; field_simp; try ring

theorem base_qf {n : ℕ} (M : ℚ) (v : Fin n → ℝ) :
    v ⬝ᵥ ((QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf n M)) *ᵥ v)
      = ((M : ℝ))⁻¹ * (v ⬝ᵥ v) := by
  rw [QMCLeafB.Boundary.castM_initShapeOf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Matrix.one_mulVec]

/-- **One engine step multiplies the quadratic form by at most `κ = ((n+1)/(n+ρ))²`.** -/
theorem qf_step_le {n : ℕ} (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {ρ : ℝ} (hρ : 0 ≤ ρ) (v : Fin n → ℝ) :
    v ⬝ᵥ (stepShape n A c p ρ *ᵥ v)
      ≤ ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ρ) ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hcs := cauchy_sigmaR hA hAp hc v
  have hβ : 0 ≤ betaR n := betaR_nonneg hn
  have hkey : (betaR n / sigmaR c p) * (c ⬝ᵥ v) ^ 2 ≤ betaR n * (v ⬝ᵥ (A *ᵥ v)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hσ]
    nlinarith [hcs]
  have hα : 0 ≤ alphaR n ρ := by
    rw [alphaR]
    apply div_nonneg
    · have := natCast_two_le hn; nlinarith
    · positivity
  rw [qf_stepShape, ← alphaR_one_add_betaR hn]
  nlinarith [hkey, hα]


/-! ## 3.  The Loewner ceiling and the `σ` floor, for ANY stream at a fixed depth -/

theorem witOf_irrel {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    (h1 h2 : QMCLeafB.EngineIterates.PosQ A) (v : Fin N → ℚ) :
    QMCLeafB.RunPartsShallow.witOf h1 v = QMCLeafB.RunPartsShallow.witOf h2 v := by
  unfold QMCLeafB.RunPartsShallow.witOf
  rw [Subsingleton.elim (QMCLeafB.RunPartsShallow.exists_mulVec_eq_of_posQ h1 v)
    (QMCLeafB.RunPartsShallow.exists_mulVec_eq_of_posQ h2 v)]


/-- **The Loewner ceiling**: along ANY stream at the fixed depth `ρ`, the quadratic form of the
engine's shape shrinks by at most `κ = ((n+1)/(n+ρ))²` per round. -/
theorem qf_le_pow {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef) {cd : ℕ → QMCLeafB.EngineIterates.CutData n}
    (hwit : ∀ k, QMCLeafB.EngineIterates.Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ0 : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0) {M0 ρ : ℚ}
    (hρ : ∀ k, (cd k).rho = ρ)
    (hbase : ∀ v : Fin n → ℝ, v ⬝ᵥ (QMCLeafB.EngineIterates.castM A0 *ᵥ v)
      = (((M0 : ℚ)) : ℝ)⁻¹ * (v ⬝ᵥ v)) (k : ℕ) (v : Fin n → ℝ) :
    v ⬝ᵥ (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd k) *ᵥ v)
      ≤ (((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2) ^ k
        * ((((M0 : ℚ)) : ℝ)⁻¹ * (v ⬝ᵥ v)) := by
  induction k with
  | zero =>
      rw [show QMCLeafB.EngineIterates.Aat n A0 cd 0 = A0 from rfl, hbase v, pow_zero,
        one_mul]
  | succ k ih =>
      have hpos : (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd k)).PosDef :=
        QMCLeafB.EngineIterates.Aat_cast_posDef hn hA0 hwit hρ0 hcne k
      have hstep := qf_step_le hn hpos (QMCLeafB.EngineIterates.cast_normal_ne (hcne k))
        (QMCLeafB.EngineIterates.cast_witness hwit k) (ρ := (((cd k).rho : ℚ) : ℝ))
        (by exact_mod_cast hρ0 k) (v := v)
      have hρc : (((cd k).rho : ℚ) : ℝ) = ((ρ : ℚ) : ℝ) := by rw [hρ k]
      have hκ : 0 ≤ ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2 := by positivity
      rw [QMCLeafB.EngineIterates.Aat_unfold, QMCLeafB.EngineIterates.rStep_cast]
      calc v ⬝ᵥ (QMCLeafB.EngineIterates.stepShape n
              (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd k))
              (fun i => (((cd k).c i : ℚ) : ℝ)) (fun i => (((cd k).p i : ℚ) : ℝ))
              ((((cd k).rho : ℚ) : ℝ)) *ᵥ v)
          ≤ ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((((cd k).rho : ℚ) : ℝ))) ^ 2
              * (v ⬝ᵥ (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd k) *ᵥ v)) := hstep
        _ = ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2
              * (v ⬝ᵥ (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd k) *ᵥ v)) := by
            rw [hρc]
        _ ≤ ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2
              * ((((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2) ^ k
                * ((((M0 : ℚ)) : ℝ)⁻¹ * (v ⬝ᵥ v))) :=
            mul_le_mul_of_nonneg_left ih hκ
        _ = (((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2) ^ (k + 1)
              * ((((M0 : ℚ)) : ℝ)⁻¹ * (v ⬝ᵥ v)) := by ring

/-- **The `σ` floor**: at a unit normal, `σ = c ⬝ᵥ p` is at least `M₀·((n+ρ)/(n+1))^{2k}` along any
stream at the fixed depth `ρ`.  (Cauchy–Schwarz in the shape metric against the Loewner ceiling.) -/
theorem sigma_ge {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef) {cd : ℕ → QMCLeafB.EngineIterates.CutData n}
    (hwit : ∀ k, QMCLeafB.EngineIterates.Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ0 : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0) {M0 ρ : ℚ}
    (hρ : ∀ k, (cd k).rho = ρ) (hM0 : 0 < M0)
    (hbase : ∀ v : Fin n → ℝ, v ⬝ᵥ (QMCLeafB.EngineIterates.castM A0 *ᵥ v)
      = (((M0 : ℚ)) : ℝ)⁻¹ * (v ⬝ᵥ v)) (k : ℕ)
    (hcsq : QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ QMCLeafB.EngineIterates.cutCR cd k = 1) :
    (((M0 : ℚ)) : ℝ) * ((((n : ℝ) + ((ρ : ℚ) : ℝ)) / ((n : ℝ) + 1)) ^ (2 * k))
      ≤ QMCLeafB.EngineIterates.sigmaR (QMCLeafB.EngineIterates.cutCR cd k)
          (QMCLeafB.EngineIterates.cutPR cd k) := by
  have hpos : (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd k)).PosDef :=
    QMCLeafB.EngineIterates.Aat_cast_posDef hn hA0 hwit hρ0 hcne k
  have hcw := QMCLeafB.EngineIterates.cast_witness hwit k
  have hcne' := QMCLeafB.EngineIterates.cast_normal_ne (hcne k)
  have hσpos := QMCLeafB.EngineIterates.sigmaR_pos hpos hcw hcne'
  have hcs := QMCLeafB.EngineIterates.cauchy_sigmaR hpos hcw hcne'
    (QMCLeafB.EngineIterates.cutCR cd k)
  have hb := qf_le_pow hn hA0 hwit hρ0 hcne hρ hbase k
    (QMCLeafB.EngineIterates.cutCR cd k)
  have h1 : (1 : ℝ) ≤ QMCLeafB.EngineIterates.sigmaR (QMCLeafB.EngineIterates.cutCR cd k)
      (QMCLeafB.EngineIterates.cutPR cd k)
      * (QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
        (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd k) *ᵥ
          QMCLeafB.EngineIterates.cutCR cd k)) := by
    simpa [hcsq] using hcs
  have h2 : QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
      (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd k) *ᵥ
        QMCLeafB.EngineIterates.cutCR cd k)
      ≤ (((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2) ^ k * ((((M0 : ℚ)) : ℝ)⁻¹) := by
    simpa [hcsq] using hb
  have hσle : QMCLeafB.EngineIterates.sigmaR (QMCLeafB.EngineIterates.cutCR cd k)
      (QMCLeafB.EngineIterates.cutPR cd k)
      * ((((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2) ^ k) * (((M0 : ℚ)) : ℝ)⁻¹
      ≥ 1 := by
    have := mul_le_mul_of_nonneg_left h2 hσpos.le
    calc (1:ℝ) ≤ QMCLeafB.EngineIterates.sigmaR (QMCLeafB.EngineIterates.cutCR cd k)
          (QMCLeafB.EngineIterates.cutPR cd k)
          * (QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
            (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd k) *ᵥ
              QMCLeafB.EngineIterates.cutCR cd k)) := h1
      _ ≤ QMCLeafB.EngineIterates.sigmaR (QMCLeafB.EngineIterates.cutCR cd k)
          (QMCLeafB.EngineIterates.cutPR cd k)
          * ((((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2) ^ k * (((M0 : ℚ)) : ℝ)⁻¹) := this
      _ = QMCLeafB.EngineIterates.sigmaR (QMCLeafB.EngineIterates.cutCR cd k)
          (QMCLeafB.EngineIterates.cutPR cd k)
          * ((((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2) ^ k) * (((M0 : ℚ)) : ℝ)⁻¹ := by ring
  set σ := QMCLeafB.EngineIterates.sigmaR (QMCLeafB.EngineIterates.cutCR cd k)
    (QMCLeafB.EngineIterates.cutPR cd k) with hσdef
  set κ : ℝ := ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + ((ρ : ℚ) : ℝ)) ^ 2 with hκdef
  set ψ : ℝ := ((n : ℝ) + ((ρ : ℚ) : ℝ)) / ((n : ℝ) + 1) with hψdef
  have hM0R : (0 : ℝ) < ((M0 : ℚ) : ℝ) := by exact_mod_cast hM0
  have hρR : (0 : ℝ) ≤ ((ρ : ℚ) : ℝ) := by
    rw [← hρ 0]; exact_mod_cast hρ0 0
  have hnR : (2 : ℝ) ≤ (n : ℝ) := natCast_two_le hn
  have hden : (0 : ℝ) < (n : ℝ) + ((ρ : ℚ) : ℝ) := by linarith
  have hnum : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hκpos : 0 < κ := by
    rw [hκdef]; apply div_pos (by positivity) (by positivity)
  have hψpos : 0 < ψ := by
    rw [hψdef]; apply div_pos hden hnum
  have hκψ : κ * ψ ^ 2 = 1 := by
    rw [hκdef, hψdef]
    field_simp
  have hMle : ((M0 : ℚ) : ℝ) ≤ σ * κ ^ k := by
    have h := mul_le_mul_of_nonneg_right hσle hM0R.le
    rw [one_mul] at h
    have hMne : ((M0 : ℚ) : ℝ) ≠ 0 := ne_of_gt hM0R
    field_simp at h ⊢
    nlinarith [h]
  have hκψk : κ ^ k * ψ ^ (2 * k) = 1 := by
    have h := congrArg (fun x : ℝ => x ^ k) hκψ
    simpa [mul_pow, pow_mul] using h
  calc ((M0 : ℚ) : ℝ) * ψ ^ (2 * k) ≤ (σ * κ ^ k) * ψ ^ (2 * k) := by
        apply mul_le_mul_of_nonneg_right hMle (pow_nonneg hψpos.le _)
    _ = σ * (κ ^ k * ψ ^ (2 * k)) := by ring
    _ = σ := by rw [hκψk, mul_one]


/-! ## 4.  The separation: the swinging diagonal cut is shallow at EVERY round -/

theorem dir_ne (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (i : Fin G.n) (k : ℕ) : dir G P hn i k ≠ 0 := by
  have hs : (if (st G P hn i k).2 ≤ 1 then (1 : ℚ) else -1) ≠ 0 := by
    split <;> norm_num
  exact smul_ne_zero hs (evec_ne i)

theorem dir_apply (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (i : Fin G.n) (k : ℕ) (j : Fin (G.n * G.n)) :
    dir G P hn i k j
      = (if (st G P hn i k).2 ≤ 1 then (1 : ℚ) else -1) * evec i j := rfl

theorem cast_dir (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (i : Fin G.n) (k : ℕ) :
    QMCLeafB.EngineIterates.cutCR (cd G P hn i) k
      = (if (st G P hn i k).2 ≤ 1 then (1 : ℝ) else -1)
        • (fun j => ((evec i j : ℚ) : ℝ)) := by
  funext j
  rw [QMCLeafB.EngineIterates.cutCR, cd_c, dir_apply, Pi.smul_apply, smul_eq_mul]
  split <;> push_cast <;> ring

/-- The relaxation pins each diagonal entry to `1 ± dq/4`, so a diagonal-coordinate cut has depth
`dq/4` at worst — independently of where the centre is. -/
theorem diag_bounds {G : QuantumMaxCutEnergy.Input} {P : QMCLeafB.FinalStroke.RunParams G}
    {t : ℚ} {z : Fin (G.n * G.n) → ℝ} (hz : z ∈ relaxBallP G t P) (i : Fin G.n) :
    1 - ((P.dq : ℚ) : ℝ) / 4 ≤ z (dIdx i) ∧ z (dIdx i) ≤ 1 + ((P.dq : ℚ) : ℝ) / 4 := by
  have hdiag : |QMCLeafB.Boundary.unflat z i i - 1| ≤ ((P.dq : ℚ) : ℝ) / 4 := hz.1.2.1 i
  have h := abs_le.mp hdiag
  rw [unflat_dIdx] at h
  constructor <;> linarith [h.1, h.2]

theorem sep_cd (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (i : Fin G.n) (t : ℚ) (k : ℕ) {z : Fin (G.n * G.n) → ℝ}
    (hz : z ∈ relaxBallP G t P) :
    QMCLeafB.EngineIterates.cutCR (cd G P hn i) k
        ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (cd G P hn i) k
      - QMCLeafB.EngineIterates.cutCR (cd G P hn i) k ⬝ᵥ z ≤ ((P.dq : ℚ) : ℝ) / 4 := by
  obtain ⟨hzlo, hzhi⟩ := diag_bounds hz i
  have hcat : (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
      (cd G P hn i) k) (dIdx i) = uOf G P hn i k := Cat_cd G P hn i k
  rw [cast_dir, smul_dotProduct, smul_dotProduct, cast_evec_dot i z,
    cast_evec_dot i (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
      (cd G P hn i) k), hcat, smul_eq_mul, smul_eq_mul]
  split_ifs with h
  · simp only [uOf] at h ⊢; nlinarith
  · push_neg at h
    simp only [uOf] at h ⊢; nlinarith

theorem self_cd (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (i : Fin G.n) (k : ℕ) :
    QMCLeafB.EngineIterates.cutCR (cd G P hn i) k
      ⬝ᵥ QMCLeafB.EngineIterates.cutCR (cd G P hn i) k = 1 := by
  rw [cast_dir, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, cast_evec_dot_self]
  split_ifs <;> norm_num

theorem hbaseP (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) :
    ∀ v : Fin (G.n * G.n) → ℝ,
      v ⬝ᵥ (QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G P) *ᵥ v)
        = ((((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ))⁻¹ * (v ⬝ᵥ v) := by
  intro v
  have h : QMCLeafB.RunPartsDilate.A0P G P
      = QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2) := by
    unfold QMCLeafB.RunPartsDilate.A0P QMCLeafB.RundataArith.capOf
    rfl
  rw [h]
  exact base_qf _ v

end QMCLeafB.Sc35M7

/-! ## Audits -/

#print axioms QMCLeafB.Sc35M7.Cat_cd
#print axioms QMCLeafB.Sc35M7.Aat_cd
#print axioms QMCLeafB.Sc35M7.qf_step_le
#print axioms QMCLeafB.Sc35M7.qf_le_pow
#print axioms QMCLeafB.Sc35M7.sigma_ge
#print axioms QMCLeafB.Sc35M7.sep_cd
#print axioms QMCLeafB.Sc35M7.self_cd


