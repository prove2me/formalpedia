-- Prove2me | Definitions.Def_QMCLeafB_sim_loop_m6
-- name    : QMCLeafB_sim_loop_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:08:20.319179+00:00
-- url     : https://prove2.me/theorems/3cd52ae7-48ad-4570-b9dc-8f008e4dc988
-- title:
--   QMCLeafB sim_loop_m6
-- statement:
--   # leaf B phase 8 — brick `sim-loop` (swarm `smw00sb1m`, member m6, direction d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_boundary_m2
/-
# leaf B phase 8 — brick `sim-loop` (swarm `smw00sb1m`, member m6, direction d9)

The fixed-round simulate is a loop that runs `T₀ = K·m` rounds and then reads a verdict.  Every
compiled engine theorem of `Solutions/Check_EngineIterates.lean` and `Solutions/Check_boundary_m2.lean`
quantifies the recorded cut sequence `cd : ℕ → CutData N` over **all** of `ℕ`: `Aat_cast_posDef`,
`Aat_det`, `Aat_vol_le`, `body_containment`, `strictBody_refuted_concrete`.  A program cannot
supply an infinite sequence: it computes exactly `T₀` cuts and stops.  This file removes that
mismatch — it re-proves the chain with the cut hypotheses required only on the **prefix**
`k < T₀`, which is what a fixed-round loop actually produces:

* §1 finite positivity `Aat_cast_posDef_prefix`;
* §2 finite determinant telescoping `Aat_det_prefix`, shallow-regime growth `Aat_det_ge_prefix`;
* §3 finite volume contraction `Aat_vol_le_prefix`, `Aat_vol_below_of_halving_prefix`;
* §4 finite containment invariant `body_containment_prefix` (+ margin form)
  and the **refuted verdict from a finite cut prefix** `strictBody_refuted_prefix`;
* §5 the loop's verdict: `anyOk` (did any round report `ok`?), `anyOk_eq_true_iff`,
  `anyOk_eq_false_iff`;
* §6 the loop's three soundness theorems: `simulate_feasible_sound` (a `true` verdict carries a
  unit-diagonal PSD witness with `tr ≤ t + εw`), `simulate_refuted_sound` (a `false` verdict
  carries the refutation `t - εr ≤ tr`), `simulate_agrees_engine` (the verdict bit *is* the
  `sbit` class of a slack answer, so the loop's bit is an engine bit).

* §7 the round count: `vol_halving_K_explicit` / `vol_below_K_explicit` (the `Nat.clog 2 ⌈2Φ₀/ε⌉₊`
  factor clears the potential ratio), `simRounds n Φ₀ r m = Nat.clog 2 ⌈2Φ₀/r^{n·n}⌉₊ * m`,
  `simRounds_budget` (it satisfies the strict budget `hK`), **`halving_time_explicit`**
  (`4N` rounds halve the contraction factor at depth zero: `rho0R N 0 ≥ 1 + 1/N` by Bernoulli,
  then `√(rho0R N 0) ≥ 1 + 1/(4N)` and Bernoulli again), and `central_run_budget`, which discharges
  *both* side conditions of the refuted verdict at
  `T₀ = Nat.clog 2 ⌈2Φ₀/r^{n·n}⌉₊ * (4·(n·n))` in the central-cut regime `ρmax = 0`.

What is *not* here: the state recursion that produces `cd` from a separation-oracle function.  The
engine's centre `Cat` is irrational (`γ/√σ`), so a rational-state loop must carry a dyadic
enclosure of it (`Check_DyadicSqrt`'s `sqrtLe`/`sqrtGe`); the step, snap and oracle bricks own that
data, and this file consumes it only through the prefix hypotheses above.

No `sorry`, no `axiom`; audit at the end.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.SimLoop

open QMCLeafB.EngineIterates

/-- The slack answer's verdict bit — verbatim `QMCLeafB.SlackRoute.sbit`, restated here so that
this file does not depend on the whole slack route (`Solutions/Check_SlackRoute_m2.lean` imports
`MergeAll3_m8`, whose olean is not in the build tree).  The two definitions unfold to the same
term, so `sbit_eq` below is `rfl`. -/
def sbit {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (eng : ∀ t : ℚ, QMCLeafB.AnswerProducer.Answerε A t εw εr) (s : ℚ) : Bool :=
  match eng s with
  | .witness _ _ _ => true
  | .refuted _ => false

/-- The verdict bit of a single slack answer: `true` on the witness branch, `false` on the
refutation branch.  Definitionally the `sbit` of the constant engine. -/
def sbitAns {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {t εw εr : ℚ}
    (ans : QMCLeafB.AnswerProducer.Answerε A t εw εr) : Bool :=
  match ans with
  | .witness _ _ _ => true
  | .refuted _ => false

/-- **Bridge to the engine form**: the `sbit` of an engine at threshold `t` is the bit of its
answer at `t` (`rfl`: both are the same match).  So `simulate_agrees_engine`'s conclusion, stated
with `sbitAns`, is the engine-level statement of the closing forms. -/
theorem sbit_eq_sbitAns {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (eng : ∀ t : ℚ, QMCLeafB.AnswerProducer.Answerε A t εw εr) (t : ℚ) :
    sbit (A := A) (εw := εw) (εr := εr) eng t =
      sbitAns (A := A) (t := t) (εw := εw) (εr := εr) (eng t) := by
  cases h : eng t with
  | witness X hX htr => simp [sbit, sbitAns, h]
  | refuted hlb => simp [sbit, sbitAns, h]

variable {n : ℕ}

/-! ## 1.  The positivity chain on a finite prefix -/

/-- The witness relation casts, on the prefix `k < T`. -/
theorem cast_witness_prefix {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n} {T : ℕ}
    (hwit : ∀ k, k < T → Aat n A0 cd k *ᵥ (cd k).p = (cd k).c) {k : ℕ} (hk : k < T) :
    castM (Aat n A0 cd k) *ᵥ cutPR cd k = cutCR cd k := by
  rw [cast_mulVec, hwit k hk]

/-- **(i) on a prefix.**  Every iterate up to `T` is positive definite, from cut data recorded
only for `k < T`. -/
theorem Aat_cast_posDef_prefix {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} {T : ℕ} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, k < T → Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < T → 0 ≤ (cd k).rho) (hcne : ∀ k, k < T → (cd k).c ≠ 0) :
    ∀ k, k ≤ T → (castM (Aat n A0 cd k)).PosDef := by
  intro k
  induction k with
  | zero => intro _; exact hA0
  | succ k ih =>
      intro hk
      have hkT : k < T := by omega
      have hk' : (castM (Aat n A0 cd k)).PosDef := ih (by omega)
      rw [Aat_unfold, rStep_cast]
      refine stepShape_posDef hn hk' (cast_normal_ne (hcne k hkT))
        (cast_witness_prefix hwit hkT) ?_
      exact_mod_cast hρ k hkT

/-! ## 2.  The determinant on a finite prefix -/

/-- **Determinant telescoping on a prefix.** -/
theorem Aat_det_prefix {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} {T : ℕ} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, k < T → Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < T → 0 ≤ (cd k).rho) (hcne : ∀ k, k < T → (cd k).c ≠ 0) :
    ∀ k, k ≤ T → (castM (Aat n A0 cd k)).det
      = (castM A0).det * ∏ j ∈ Finset.range k, rho0R n ((cd j).rho : ℝ) := by
  intro k
  induction k with
  | zero => intro _; simp [Aat]
  | succ k ih =>
      intro hk
      have hkT : k < T := by omega
      have hk' := ih (by omega)
      have hpd := Aat_cast_posDef_prefix hn hA0 hwit hρ hcne k (by omega)
      rw [Aat_unfold, rStep_cast,
        stepShape_det hn hpd (cast_normal_ne (hcne k hkT)) (cast_witness_prefix hwit hkT)
          ((cd k).rho : ℝ), hk', Finset.prod_range_succ]
      ring

/-- **Determinant growth in the shallow regime, on a prefix.** -/
theorem Aat_det_ge_prefix {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} {T : ℕ} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, k < T → Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < T → 0 ≤ (cd k).rho) (hcne : ∀ k, k < T → (cd k).c ≠ 0)
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, k < T → (cd k).rho ≤ ρmax) :
    ∀ k, k ≤ T → (castM A0).det * (rho0R n (ρmax : ℝ)) ^ k ≤ (castM (Aat n A0 cd k)).det := by
  intro k hk
  rw [Aat_det_prefix hn hA0 hwit hρ hcne k hk]
  have hdet0 : (0:ℝ) ≤ (castM A0).det := hA0.det_pos.le
  have hprod : (∏ j ∈ Finset.range k, rho0R n ((ρmax : ℝ)))
      ≤ ∏ j ∈ Finset.range k, rho0R n ((cd j).rho : ℝ) := by
    refine Finset.prod_le_prod
      (fun j _ => (rho0R_pos hn (by exact_mod_cast hρmax : (0:ℝ) ≤ (ρmax : ℝ))).le)
      (fun j hj => ?_)
    have hjT : j < T := by
      have := Finset.mem_range.mp hj
      omega
    exact rho0R_anti hn (by exact_mod_cast hρ j hjT : (0:ℝ) ≤ ((cd j).rho : ℝ))
      (by exact_mod_cast hle j hjT : ((cd j).rho : ℝ) ≤ (ρmax : ℝ))
  have hconst : (∏ j ∈ Finset.range k, rho0R n ((ρmax : ℝ))) = (rho0R n (ρmax : ℝ)) ^ k := by
    simp [Finset.prod_const]
  rw [hconst] at hprod
  exact mul_le_mul_of_nonneg_left hprod hdet0

/-! ## 3.  The volume potential on a finite prefix -/

/-- **Volume contraction on a prefix.** -/
theorem Aat_vol_le_prefix {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} {T : ℕ} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, k < T → Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < T → 0 ≤ (cd k).rho) (hcne : ∀ k, k < T → (cd k).c ≠ 0)
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, k < T → (cd k).rho ≤ ρmax) :
    ∀ k, k ≤ T → volPot n (Aat n A0 cd k)
      ≤ (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ k * volPot n A0 := by
  intro k hk
  have hspos : (0:ℝ) < rho0R n (ρmax : ℝ) :=
    rho0R_pos hn (by exact_mod_cast hρmax : (0:ℝ) ≤ (ρmax : ℝ))
  have hdet0 : (0:ℝ) < (castM A0).det := hA0.det_pos
  have hdetk : (0:ℝ) < (castM (Aat n A0 cd k)).det :=
    (Aat_cast_posDef_prefix hn hA0 hwit hρ hcne k hk).det_pos
  have hge := Aat_det_ge_prefix hn hA0 hwit hρ hcne hρmax hle k hk
  have hsqrtpow : ∀ j : ℕ, Real.sqrt ((rho0R n (ρmax : ℝ)) ^ j)
      = (Real.sqrt (rho0R n (ρmax : ℝ))) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ i ih =>
        rw [pow_succ, Real.sqrt_mul (le_of_lt (pow_pos hspos i)), ih, pow_succ]
  have hsqrt : Real.sqrt ((castM A0).det * (rho0R n (ρmax : ℝ)) ^ k)
      = Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k := by
    rw [Real.sqrt_mul (le_of_lt hdet0), hsqrtpow]
  have hle' : Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k
      ≤ Real.sqrt ((castM (Aat n A0 cd k)).det) := by
    rw [← hsqrt]
    exact Real.sqrt_le_sqrt hge
  have hpos' : (0:ℝ) < Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k :=
    mul_pos (Real.sqrt_pos.2 hdet0) (pow_pos (Real.sqrt_pos.2 hspos) k)
  have hinv : (Real.sqrt ((castM (Aat n A0 cd k)).det))⁻¹
      ≤ (Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k)⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.2 hdetk) hpos').mpr hle'
  calc volPot n (Aat n A0 cd k) ≤
        (Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k)⁻¹ := hinv
    _ = (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ k * volPot n A0 := by
        rw [mul_inv, inv_pow, volPot]
        ring

/-- **The potential drops below a target, on a prefix**: the halving form of
`Aat_vol_below_of_halving` with the cut data recorded only for `k < T` (`T = K·m`). -/
theorem Aat_vol_below_of_halving_prefix {n : ℕ} (hn : 2 ≤ n)
    {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n} {T : ℕ}
    (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, k < T → Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < T → 0 ≤ (cd k).rho) (hcne : ∀ k, k < T → (cd k).c ≠ 0)
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, k < T → (cd k).rho ≤ ρmax)
    {m K : ℕ} (hm : (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    {ε : ℝ} (hK : volPot n A0 * (1 / 2) ^ K ≤ ε) (hTm : K * m ≤ T) :
    volPot n (Aat n A0 cd (K * m)) ≤ ε := by
  have hc0 : (0:ℝ) ≤ (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ := by positivity
  have h1 := Aat_vol_le_prefix hn hA0 hwit hρ hcne hρmax hle (K * m) hTm
  have hpow : (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ (K * m) ≤ (1 / 2) ^ K := by
    rw [Nat.mul_comm, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hc0 m) hm K
  have hΦ0 : (0:ℝ) ≤ volPot n A0 := (volPot_pos hA0).le
  calc volPot n (Aat n A0 cd (K * m))
      ≤ (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ (K * m) * volPot n A0 := h1
    _ ≤ (1 / 2) ^ K * volPot n A0 := mul_le_mul_of_nonneg_right hpow hΦ0
    _ = volPot n A0 * (1 / 2) ^ K := by ring
    _ ≤ ε := hK

end QMCLeafB.SimLoop

/-! ## 4.  The containment invariant on a finite prefix, and the refuted verdict

A fixed-round loop records cuts at rounds `0, …, T₀-1` and nothing more.  `body_containment`
(`Check_EngineIterates`) asks for the cut halfspace at *every* `k : ℕ`; here it is asked only on
the prefix, and then carried to the explicit round `K·m` that the loop actually runs. -/

namespace QMCLeafB.SimLoop

open QMCLeafB.EngineIterates
open QMCLeafB.Boundary

namespace Prefix

variable {n : ℕ}

/-- **(ii-a) on a prefix.**  A body covered by the initial ellipsoid and lying in the recorded cut
halfspaces of rounds `< T` stays inside every iterate's ellipsoid up to `T`. -/
theorem body_containment_prefix {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} {T : ℕ} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, k < T → Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < T → 0 ≤ (cd k).rho) (hcne : ∀ k, k < T → (cd k).c ≠ 0)
    (a0 : Fin n → ℝ) (body : (Fin n → ℝ) → Prop)
    (hcover : ∀ z, body z → Ell (castM A0) a0 z)
    (hcut : ∀ k, k < T → ∀ z, body z →
      -(((cd k).rho : ℝ) * sqrtSigmaR (cutCR cd k) (cutPR cd k)) ≤
        cutCR cd k ⬝ᵥ (z - Cat n a0 cd k)) :
    ∀ k, k ≤ T → ∀ z, body z → Ell (castM (Aat n A0 cd k)) (Cat n a0 cd k) z := by
  intro k
  induction k with
  | zero => intro _ z hz; exact hcover z hz
  | succ k ih =>
      intro hk z hz
      have hkT : k < T := by omega
      have hk' : Ell (castM (Aat n A0 cd k)) (Cat n a0 cd k) z := ih (by omega) z hz
      have hstep := step_containment hn
        (Aat_cast_posDef_prefix hn hA0 hwit hρ hcne k (by omega))
        (cast_normal_ne (hcne k hkT)) (cast_witness_prefix hwit hkT) (Cat n a0 cd k)
        (by exact_mod_cast hρ k hkT : (0:ℝ) ≤ ((cd k).rho : ℝ))
      rw [Aat_unfold, rStep_cast, Cat_unfold]
      exact hstep ⟨hk', hcut k hkT z hz⟩

/-- The containment at the explicit round `K·m`, in the oracle's absolute-margin form: only the
prefix `k < T` of the recorded cuts is used, and `K·m ≤ T`. -/
theorem body_containment_at_halving_margin_prefix {n : ℕ} (hn : 2 ≤ n)
    {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n} {T : ℕ}
    (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, k < T → Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < T → 0 ≤ (cd k).rho) (hcne : ∀ k, k < T → (cd k).c ≠ 0)
    (a0 : Fin n → ℝ) (body : (Fin n → ℝ) → Prop)
    (hcover : ∀ z, body z → Ell (castM A0) a0 z)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, k < T → 0 ≤ δ k)
    (hcheck : ∀ k, k < T → (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k, k < T → ∀ z, body z →
      -(((δ k : ℚ)) : ℝ) ≤ cutCR cd k ⬝ᵥ (z - Cat n a0 cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, k < T → (cd k).rho ≤ ρmax)
    {m K : ℕ} (hm : (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    {ε : ℝ} (hK : volPot n A0 * (1 / 2) ^ K ≤ ε) (hTm : K * m ≤ T) :
    (∀ z, body z → Ell (castM (Aat n A0 cd (K * m))) (Cat n a0 cd (K * m)) z) ∧
      volPot n (Aat n A0 cd (K * m)) ≤ ε := by
  have hcut : ∀ k, k < T → ∀ z, body z →
      -(((cd k).rho : ℝ) * sqrtSigmaR (cutCR cd k) (cutPR cd k)) ≤
        cutCR cd k ⬝ᵥ (z - Cat n a0 cd k) := by
    intro k hkT z hz
    have hσR : 0 < sigmaR (cutCR cd k) (cutPR cd k) :=
      sigmaR_pos (Aat_cast_posDef_prefix hn hA0 hwit hρ hcne k (by omega))
        (cast_witness_prefix hwit hkT) (cast_normal_ne (hcne k hkT))
    have hδle : (((δ k : ℚ)) : ℝ)
        ≤ ((cd k).rho : ℝ) * Real.sqrt ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ) :=
      margin_le_of_sq_check (hδ0 k hkT) (hρ k hkT) (sigmaQ_pos_of_cast hσR).le (hcheck k hkT)
    have hσeq : ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ) = sigmaR (cutCR cd k) (cutPR cd k) :=
      cast_sigmaQ (cd k).c (cd k).p
    rw [hσeq] at hδle
    exact le_trans (neg_le_neg hδle) (hcutδ k hkT z hz)
  exact ⟨body_containment_prefix hn hA0 hwit hρ hcne a0 body hcover hcut (K * m) hTm,
    Aat_vol_below_of_halving_prefix hn hA0 hwit hρ hcne hρmax hle hm hK hTm⟩

/-- **The refuted verdict from a finite cut prefix.**  Same conclusion as
`Check_boundary_m2`'s `strictBody_refuted_at_halving`, but every cut hypothesis is asked only for
`k < K·m` — the rounds the loop runs.  `W` is the ball-carrying relaxation the oracle separates
(not `StrictBody` itself). -/
theorem strictBody_refuted_prefix {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (t εr : ℚ)
    (M : ℚ) (hM : 0 < M)
    (W : (Fin (n * n) → ℝ) → Prop)
    (hWbound : ∀ z, W z → ∑ i, z i ^ 2 ≤ (M : ℝ))
    (cd : ℕ → CutData (n * n))
    {m K : ℕ}
    (hwit : ∀ k, k < K * m →
      Aat (n * n) (initShapeOf (n * n) M) cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < K * m → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < K * m → (cd k).c ≠ 0)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, k < K * m → 0 ≤ δ k)
    (hcheck : ∀ k, k < K * m → (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k, k < K * m → ∀ z, W z →
      -(((δ k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (n * n) (0 : Fin (n * n) → ℝ) cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, k < K * m → (cd k).rho ≤ ρmax)
    (hm : (Real.sqrt (rho0R (n * n) (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    {r : ℝ} (hr : 0 < r)
    (hK : volPot (n * n) (initShapeOf (n * n) M) * (1 / 2) ^ K < r ^ (n * n))
    (hball : ∀ u, QMCLeafB.AnswerProducer.StrictBody A t εr u → eucBallF u r ⊆ W) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace := by
  classical
  have hn' : 2 ≤ n * n := by nlinarith
  have hA0 : (castM (initShapeOf (n * n) M)).PosDef := initShapeOf_cast_posDef hM
  obtain ⟨hcover, hsmallle⟩ :
      (∀ z, W z → Ell (castM (Aat (n * n) (initShapeOf (n * n) M) cd (K * m)))
          (Cat (n * n) (0 : Fin (n * n) → ℝ) cd (K * m)) z) ∧
      volPot (n * n) (Aat (n * n) (initShapeOf (n * n) M) cd (K * m))
        ≤ volPot (n * n) (initShapeOf (n * n) M) * (1 / 2) ^ K :=
    body_containment_at_halving_margin_prefix (n := n * n) hn' hA0 hwit hρ hcne
      (0 : Fin (n * n) → ℝ) W (fun z hz => ell_initShapeOf hM (hWbound z hz))
      hδ0 hcheck hcutδ hρmax hle hm le_rfl le_rfl
  have hKpd : (castM (Aat (n * n) (initShapeOf (n * n) M) cd (K * m))).PosDef :=
    Aat_cast_posDef_prefix hn' hA0 hwit hρ hcne (K * m) le_rfl
  have hsmall : QMCLeafB.AnswerProducer.volPot
      (castM (Aat (n * n) (initShapeOf (n * n) M) cd (K * m))) < r ^ (n * n) :=
    lt_of_le_of_lt hsmallle hK
  intro Z hZ
  by_contra hcon
  have htr : (A * Z).trace ≤ (t : ℝ) - (εr : ℝ) := le_of_lt (not_le.mp hcon)
  have hmem : QMCLeafB.AnswerProducer.StrictBody A t εr (QMCLeafB.AnswerProducer.flat Z) :=
    ⟨Z, hZ, htr, rfl⟩
  have hballZ : eucBallF (QMCLeafB.AnswerProducer.flat Z) r ⊆
      Ell (castM (Aat (n * n) (initShapeOf (n * n) M) cd (K * m)))
        (Cat (n * n) (0 : Fin (n * n) → ℝ) cd (K * m)) :=
    fun w hw => hcover w (hball (QMCLeafB.AnswerProducer.flat Z) hmem hw)
  have hdet : r ^ (2 * (n * n)) *
      (castM (Aat (n * n) (initShapeOf (n * n) M) cd (K * m))).det ≤ 1 :=
    QMCLeafB.BallFloor.pow_two_mul_det_le_one_of_ball_subset_Ell (n := n * n)
      (A := castM (Aat (n * n) (initShapeOf (n * n) M) cd (K * m)))
      (a := Cat (n * n) (0 : Fin (n * n) → ℝ) cd (K * m))
      (a₀ := QMCLeafB.AnswerProducer.flat Z) hKpd hr
      (fun y hy => hballZ (by
        show ∑ i, ((y + QMCLeafB.AnswerProducer.flat Z) i
          - QMCLeafB.AnswerProducer.flat Z i) ^ 2 ≤ r ^ 2
        simpa using hy))
  have hle : r ^ (n * n) ≤ QMCLeafB.AnswerProducer.volPot
      (castM (Aat (n * n) (initShapeOf (n * n) M) cd (K * m))) := by
    simpa using
      (QMCLeafB.AnswerProducer.rpow_le_volPot (ι := Fin (n * n)) hr hKpd (by simpa using hdet))
  exact absurd (lt_of_lt_of_le hsmall hle) (lt_irrefl _)

/-- **The refuted verdict from a finite cut prefix, with the campaign's radius.**  The
`Soundε`-shaped refutation (`t - εr ≤ tr` for every unit-diagonal PSD `Z`) obtained from the
prefix `k < K·m` of recorded cuts, with the relaxation radius `M = 2n² + 2δ²` and the ball floor
of `Check_ball_floor` plugged in.  This is `Check_boundary_m2`'s `strictBody_refuted_concrete`
with the infinite cut sequence replaced by a finite one. -/
theorem strictBody_refuted_prefix_concrete {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (t εr : ℚ)
    (δq cAq : ℚ) (hδq : 0 < δq) (hcAq : 0 ≤ cAq)
    (hAsum : ∑ i, ∑ j, |A i j| ≤ (cAq : ℝ))
    (cd : ℕ → CutData (n * n))
    {m K : ℕ}
    (hwit : ∀ k, k < K * m →
      Aat (n * n) (initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2)) cd k
        *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < K * m → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < K * m → (cd k).c ≠ 0)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, k < K * m → 0 ≤ δ k)
    (hcheck : ∀ k, k < K * m → (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k, k < K * m → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall A ((t : ℝ) - (εr : ℝ)) (δq : ℝ)
        ((2 * (n : ℚ) ^ 2 + 2 * δq ^ 2 : ℚ) : ℝ) →
      -(((δ k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (n * n) (0 : Fin (n * n) → ℝ) cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, k < K * m → (cd k).rho ≤ ρmax)
    (hm : (Real.sqrt (rho0R (n * n) (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (hK : volPot (n * n) (initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2)) * (1 / 2) ^ K
      < ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n)) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace := by
  obtain ⟨hMpos, hMbig⟩ := QMCLeafB.Boundary.exists_M (n := n) (by omega) hδq hcAq
  have hδR : (0 : ℝ) < (δq : ℝ) := by exact_mod_cast hδq
  have hcAR : (0 : ℝ) ≤ (cAq : ℝ) := by exact_mod_cast hcAq
  refine strictBody_refuted_prefix hn A t εr (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2) hMpos
    (QMCLeafB.Boundary.relaxBall A ((t : ℝ) - (εr : ℝ)) (δq : ℝ)
      ((2 * (n : ℚ) ^ 2 + 2 * δq ^ 2 : ℚ) : ℝ))
    (fun z hz => hz.2) cd hwit hρ hcne hδ0 hcheck hcutδ hρmax hle hm
    (by positivity) hK ?_
  intro u hu
  exact QMCLeafB.Boundary.strictBody_ball_relaxBall hδR hcAR hAsum hMbig hu

end Prefix

end QMCLeafB.SimLoop

namespace QMCLeafB.SimLoop

open QMCLeafB.EngineIterates
open QMCLeafB.Boundary

/-! ## 5.  The loop's verdict bit

The simulate is a fixed round counter `T = K·m` over an oracle that reports, at every round, whether
the centre passes the shifted feasibility test.  The verdict of the run is the Boolean "some round
reported `ok`".  Nothing else is read out of the run: the refutation branch uses the recorded cuts,
the feasible branch uses the certificate of the round that reported `ok`. -/

/-- The verdict of a `T`-round run: `true` iff some round `k < T` reported `ok`. -/
def anyOk (ok : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | (k + 1) => ok k || anyOk ok k

theorem anyOk_succ (ok : ℕ → Bool) (k : ℕ) :
    anyOk ok (k + 1) = (ok k || anyOk ok k) := rfl

/-- A `true` verdict names the round that reported `ok`. -/
theorem anyOk_eq_true_iff (ok : ℕ → Bool) :
    ∀ T : ℕ, anyOk ok T = true ↔ ∃ k, k < T ∧ ok k = true
  | 0 => by simp [anyOk]
  | (k + 1) => by
      rw [anyOk_succ, Bool.or_eq_true, anyOk_eq_true_iff ok k]
      constructor
      · rintro (h | ⟨j, hj, hok⟩)
        · exact ⟨k, by omega, h⟩
        · exact ⟨j, by omega, hok⟩
      · rintro ⟨j, hj, hok⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
        · exact Or.inr ⟨j, hj', hok⟩
        · exact Or.inl hok

/-- A `false` verdict says every round reported a cut. -/
theorem anyOk_eq_false_iff (ok : ℕ → Bool) :
    ∀ T : ℕ, anyOk ok T = false ↔ ∀ k, k < T → ok k = false
  | 0 => by simp [anyOk]
  | (k + 1) => by
      rw [anyOk_succ, Bool.or_eq_false_iff, anyOk_eq_false_iff ok k]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
        · exact h2 j hj'
        · exact h1
      · intro h
        exact ⟨h k (by omega), fun j hj => h j (by omega)⟩

/-! ## 6.  The loop's soundness theorems

The three statements the brief names, at a fixed round count `T = K·m`:

* `simulate_feasible_sound` — a `true` verdict carries a unit-diagonal semidefinite point whose
  trace is at most `t + εw`;
* `simulate_refuted_sound` — a `false` verdict carries the refutation `t - εr ≤ tr` for every
  unit-diagonal semidefinite point, from the *finite* prefix of cuts the loop recorded;
* `simulate_agrees_engine` — the verdict bit is the `sbit` of a slack answer, i.e. the loop decides
  exactly what a sound engine decides at threshold `t`. -/

/-- **The feasible verdict is sound.** -/
theorem simulate_feasible_sound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {t εw : ℚ}
    {ok : ℕ → Bool} {T : ℕ}
    (hcert : ∀ k, k < T → ok k = true →
      ∃ X : Matrix (Fin n) (Fin n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ) + (εw : ℝ))
    (hv : anyOk ok T = true) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ) + (εw : ℝ) := by
  obtain ⟨k, hk, hok⟩ := (anyOk_eq_true_iff ok T).mp hv
  exact hcert k hk hok

/-- **The refuted verdict is sound**, from the finite cut prefix `k < K·m`: the loop's `false`
verdict is `strictBody_refuted_prefix_concrete`, with the round-level facts supplied exactly on the
rounds where the oracle reported a cut. -/
theorem simulate_refuted_sound {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (t εr : ℚ)
    (δq cAq : ℚ) (hδq : 0 < δq) (hcAq : 0 ≤ cAq)
    (hAsum : ∑ i, ∑ j, |A i j| ≤ (cAq : ℝ))
    (ok : ℕ → Bool) {m K : ℕ} (cd : ℕ → CutData (n * n))
    (hwit : ∀ k, k < K * m → ok k = false →
      Aat (n * n) (initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2)) cd k
        *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < K * m → ok k = false → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < K * m → ok k = false → (cd k).c ≠ 0)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, k < K * m → ok k = false → 0 ≤ δ k)
    (hcheck : ∀ k, k < K * m → ok k = false →
      (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k, k < K * m → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall A ((t : ℝ) - (εr : ℝ)) (δq : ℝ)
        ((2 * (n : ℚ) ^ 2 + 2 * δq ^ 2 : ℚ) : ℝ) →
      -(((δ k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (n * n) (0 : Fin (n * n) → ℝ) cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax)
    (hle : ∀ k, k < K * m → ok k = false → (cd k).rho ≤ ρmax)
    (hm : (Real.sqrt (rho0R (n * n) (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (hK : volPot (n * n) (initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2)) * (1 / 2) ^ K
      < ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n))
    (hv : anyOk ok (K * m) = false) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace := by
  have hfalse : ∀ k, k < K * m → ok k = false := (anyOk_eq_false_iff ok (K * m)).mp hv
  exact Prefix.strictBody_refuted_prefix_concrete hn A t εr δq cAq hδq hcAq hAsum cd
    (fun k hk => hwit k hk (hfalse k hk)) (fun k hk => hρ k hk (hfalse k hk))
    (fun k hk => hcne k hk (hfalse k hk)) (fun k hk => hδ0 k hk (hfalse k hk))
    (fun k hk => hcheck k hk (hfalse k hk)) (fun k hk => hcutδ k hk (hfalse k hk))
    hρmax (fun k hk => hle k hk (hfalse k hk)) hm hK

/-- **The loop decides what a sound engine decides.**  The verdict bit of the `T`-round run is the
`sbit` of a slack answer at the same threshold and the same slacks: the two verdict classes agree,
so the loop's bit is an engine bit in the sense of the closing forms. -/
theorem simulate_agrees_engine {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {t εw εr : ℚ}
    {ok : ℕ → Bool} {T : ℕ}
    (hfeas : anyOk ok T = true →
      ∃ X : Matrix (Fin n) (Fin n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ) + (εw : ℝ))
    (href : anyOk ok T = false → ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace) :
    ∃ ans : QMCLeafB.AnswerProducer.Answerε A t εw εr, sbitAns ans = anyOk ok T := by
  cases h : anyOk ok T with
  | true =>
      obtain ⟨X, hX, htr⟩ := hfeas h
      exact ⟨QMCLeafB.AnswerProducer.Answerε.witness X hX htr, by simp [sbitAns]⟩
  | false =>
      exact ⟨QMCLeafB.AnswerProducer.Answerε.refuted (href h), by simp [sbitAns]⟩

/-- **The loop's verdict is an engine answer.**  Both branches in one statement: the `T`-round run
produces an `Answerε` whose `sbit` is the run's verdict, with the feasible branch from the round
certificates and the refuted branch from the finite cut prefix. -/
theorem simulate_sound {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (t εw εr : ℚ)
    (δq cAq : ℚ) (hδq : 0 < δq) (hcAq : 0 ≤ cAq)
    (hAsum : ∑ i, ∑ j, |A i j| ≤ (cAq : ℝ))
    (ok : ℕ → Bool) {m K : ℕ} (cd : ℕ → CutData (n * n))
    (hcert : ∀ k, k < K * m → ok k = true →
      ∃ X : Matrix (Fin n) (Fin n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ) + (εw : ℝ))
    (hwit : ∀ k, k < K * m → ok k = false →
      Aat (n * n) (initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2)) cd k
        *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, k < K * m → ok k = false → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < K * m → ok k = false → (cd k).c ≠ 0)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, k < K * m → ok k = false → 0 ≤ δ k)
    (hcheck : ∀ k, k < K * m → ok k = false →
      (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k, k < K * m → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall A ((t : ℝ) - (εr : ℝ)) (δq : ℝ)
        ((2 * (n : ℚ) ^ 2 + 2 * δq ^ 2 : ℚ) : ℝ) →
      -(((δ k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (n * n) (0 : Fin (n * n) → ℝ) cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax)
    (hle : ∀ k, k < K * m → ok k = false → (cd k).rho ≤ ρmax)
    (hm : (Real.sqrt (rho0R (n * n) (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (hK : volPot (n * n) (initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2)) * (1 / 2) ^ K
      < ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n)) :
    ∃ ans : QMCLeafB.AnswerProducer.Answerε A t εw εr, sbitAns ans = anyOk ok (K * m) :=
  simulate_agrees_engine
    (fun hv => simulate_feasible_sound hcert hv)
    (fun hv => simulate_refuted_sound hn A t εr δq cAq hδq hcAq hAsum ok cd hwit hρ hcne
      hδ0 hcheck hcutδ hρmax hle hm hK hv)

/-! ## 7.  The round count `K` as a closed `Nat.clog 2` expression

The loop cannot search for its round count.  `exists_rounds` (boundary-m2) only produces one
existentially; here the `K` of the halving form is written down, `Nat.clog 2 ⌈2Φ₀/ε⌉₊`, and proved
to clear the ratio — so `T₀ = K * m` has one explicit factor and one (the halving time `m` of the
contraction factor, supplied by `exists_halving_time`) that the caller extracts. -/

/-- **The explicit `K` clears the potential ratio.**  `Φ₀ * 2^{-K} ≤ ε` at
`K = Nat.clog 2 ⌈Φ₀/ε⌉₊`. -/
theorem vol_halving_K_explicit {Φ₀ ε : ℝ} (hΦ : 0 < Φ₀) (hε : 0 < ε) :
    Φ₀ * (1 / 2) ^ (Nat.clog 2 ⌈Φ₀ / ε⌉₊) ≤ ε := by
  set K := Nat.clog 2 ⌈Φ₀ / ε⌉₊
  have hratio : 0 < Φ₀ / ε := div_pos hΦ hε
  have hceil0 : 0 < ⌈Φ₀ / ε⌉₊ := Nat.ceil_pos.mpr hratio
  have h2K : ((⌈Φ₀ / ε⌉₊ : ℕ) : ℝ) ≤ 2 ^ K := by
    have h := Nat.le_pow_clog (b := 2) (by norm_num) ⌈Φ₀ / ε⌉₊
    have h' : ((⌈Φ₀ / ε⌉₊ : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hle : Φ₀ / ε ≤ 2 ^ K := le_trans (Nat.le_ceil (Φ₀ / ε)) h2K
  have hΦle : Φ₀ ≤ 2 ^ K * ε := by
    rw [div_le_iff₀ hε] at hle
    linarith
  have hpos : (0:ℝ) < 2 ^ K := by positivity
  calc Φ₀ * (1 / 2) ^ K ≤ (2 ^ K * ε) * (1 / 2) ^ K := by
        exact mul_le_mul_of_nonneg_right hΦle (by positivity)
    _ = ε := by
        rw [one_div, inv_pow, mul_right_comm, mul_inv_cancel₀ (by positivity), one_mul]

/-- **The explicit `K` clears a strict target.**  At `K = Nat.clog 2 ⌈2Φ₀/ε⌉₊` the potential is
strictly below `ε` — the shape the refuted verdict (`strictBody_refuted_prefix_concrete`) asks
for. -/
theorem vol_below_K_explicit {Φ₀ ε : ℝ} (hΦ : 0 < Φ₀) (hε : 0 < ε) :
    Φ₀ * (1 / 2) ^ (Nat.clog 2 ⌈2 * Φ₀ / ε⌉₊) < ε := by
  have h2 : (0:ℝ) < 2 * Φ₀ := by linarith
  have hle := vol_halving_K_explicit h2 hε
  have hx0 : (0:ℝ) < (1 / 2) ^ (Nat.clog 2 ⌈2 * Φ₀ / ε⌉₊) := by positivity
  nlinarith [hle, hΦ, hx0]

/-- **The round count of the loop.**  `T₀ = K * m`: `K` is the closed `Nat.clog 2` expression that
clears the potential ratio `Φ₀/r^{n²}`, `m` the halving time of the contraction factor. -/
noncomputable def simRounds (n : ℕ) (Φ₀ r : ℝ) (m : ℕ) : ℕ :=
  Nat.clog 2 ⌈2 * Φ₀ / r ^ (n * n)⌉₊ * m

/-- **The loop's round count works.**  For the campaign's radius `r = δ/(8(c_A+1))` and initial
potential `Φ₀ = volPot (n*n) (initShapeOf (n*n) M)`, the explicit count `simRounds` satisfies the
strict budget `hK` of the refuted verdict, so `simulate_refuted_sound` can be run at
`K = Nat.clog 2 ⌈2Φ₀/r^{n²}⌉₊` with no search. -/
theorem simRounds_budget {n : ℕ} (M : ℚ) (hM : 0 < M) {δq cAq : ℚ} (hδq : 0 < δq)
    (hcAq : 0 ≤ cAq) {m : ℕ} (hm1 : 1 ≤ m) :
    volPot (n * n) (initShapeOf (n * n) M)
        * (1 / 2) ^ (simRounds n (volPot (n * n) (initShapeOf (n * n) M))
            ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) m) <
      ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n) := by
  set Φ₀ := volPot (n * n) (initShapeOf (n * n) M) with hΦ₀
  set r : ℝ := (δq : ℝ) / (8 * ((cAq : ℝ) + 1)) with hrdef
  have hΦ : 0 < Φ₀ := volPot_pos (initShapeOf_cast_posDef hM)
  have hr : 0 < r := by
    have h1 : (0:ℝ) < (δq : ℝ) := by exact_mod_cast hδq
    have h2 : (0:ℝ) < (cAq : ℝ) + 1 := by
      have : (0:ℝ) ≤ (cAq : ℝ) := by exact_mod_cast hcAq
      linarith
    rw [hrdef]
    positivity
  have hbase : Φ₀ * (1 / 2) ^ (Nat.clog 2 ⌈2 * Φ₀ / r ^ (n * n)⌉₊) < r ^ (n * n) :=
    vol_below_K_explicit hΦ (pow_pos hr (n * n))
  have hmono : (1 / 2 : ℝ) ^ (Nat.clog 2 ⌈2 * Φ₀ / r ^ (n * n)⌉₊ * m)
      ≤ (1 / 2) ^ (Nat.clog 2 ⌈2 * Φ₀ / r ^ (n * n)⌉₊) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.le_mul_of_pos_right _ (by omega))
  have hstep : Φ₀ * (1 / 2) ^ (Nat.clog 2 ⌈2 * Φ₀ / r ^ (n * n)⌉₊ * m)
      ≤ Φ₀ * (1 / 2) ^ (Nat.clog 2 ⌈2 * Φ₀ / r ^ (n * n)⌉₊) :=
    mul_le_mul_of_nonneg_left hmono hΦ.le
  exact lt_of_le_of_lt hstep hbase

/-- `rho0` at depth zero is at least `1 + 1/N`. -/
theorem rho0R_zero_ge_one_add {N : ℕ} (hN : 2 ≤ N) :
    1 + ((N : ℝ))⁻¹ ≤ rho0R N 0 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0 : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNm1 : (N:ℝ) - 1 ≠ 0 := by linarith
  have hu1 : ((N:ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hNpos]
    exact_mod_cast (by omega : 1 ≤ N)
  have hu0 : (0:ℝ) ≤ ((N:ℝ))⁻¹ := le_of_lt (inv_pos.mpr hNpos)
  have hsq2 : ((N:ℝ))⁻¹ ^ 2 ≤ 2 := by
    have h := pow_le_pow_left₀ hu0 hu1 2
    norm_num at h
    rw [inv_pow]
    linarith
  have hbern : 1 - ((N:ℝ))⁻¹ ≤ (1 - ((N:ℝ) ^ 2)⁻¹) ^ N := by
    have hsmall : ((N:ℝ) ^ 2)⁻¹ ≤ 2 := by
      rw [← inv_pow]
      exact hsq2
    have h := one_add_mul_le_pow (a := -(((N:ℝ) ^ 2)⁻¹))
      (by linarith : (-2:ℝ) ≤ -(((N:ℝ) ^ 2)⁻¹)) N
    have h1 : (1 + (N:ℝ) * -(((N:ℝ) ^ 2)⁻¹)) = 1 - ((N:ℝ))⁻¹ := by
      field_simp
      ring
    rw [h1] at h
    exact h
  have hkey : (1 - ((N:ℝ))⁻¹) * (((N:ℝ) + 1) / ((N:ℝ) - 1)) = 1 + ((N:ℝ))⁻¹ := by
    field_simp
  rw [rho0R_zero_eq hN, ← hkey]
  simp only [one_div]
  refine mul_le_mul_of_nonneg_right hbern ?_
  exact div_nonneg (by linarith) (by linarith)

/-- `1 + 1/(4N)` squares below `1 + 1/N`. -/
theorem sq_four {N : ℕ} (hN : 2 ≤ N) :
    (1 + (4 * (N:ℝ))⁻¹) ^ 2 ≤ 1 + ((N:ℝ))⁻¹ := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0 : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  field_simp
  nlinarith

/-- **Explicit halving time**: `4N` rounds halve the potential factor at depth zero. -/
theorem halving_time_explicit {N : ℕ} (hN : 2 ≤ N) :
    (Real.sqrt (rho0R N 0))⁻¹ ^ (4 * N) ≤ 1 / 2 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0 : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  have hrho := rho0R_zero_ge_one_add hN
  have hrhpos : (0:ℝ) < rho0R N 0 := by
    have : (0:ℝ) ≤ ((N:ℝ))⁻¹ := by positivity
    linarith
  have h4 : (0:ℝ) ≤ (4 * (N:ℝ))⁻¹ := by positivity
  have hbase : 1 + (4 * (N:ℝ))⁻¹ ≤ Real.sqrt (rho0R N 0) := by
    rw [Real.le_sqrt (by linarith) (le_of_lt hrhpos)]
    exact le_trans (sq_four hN) hrho
  have hb0 : (0:ℝ) ≤ 1 + (4 * (N:ℝ))⁻¹ := by linarith
  have hkeep : (4 * (N:ℝ)) * (4 * (N:ℝ))⁻¹ = 1 :=
    mul_inv_cancel₀ (by positivity)
  have hbern : 2 ≤ (1 + (4 * (N:ℝ))⁻¹) ^ (4 * N) := by
    have h := one_add_mul_le_pow (a := (4 * (N:ℝ))⁻¹) (by linarith) (4 * N)
    push_cast at h
    calc (2:ℝ) = 1 + (4 * (N:ℝ)) * (4 * (N:ℝ))⁻¹ := by rw [hkeep]; norm_num
      _ ≤ (1 + (4 * (N:ℝ))⁻¹) ^ (4 * N) := h
  have hmono : (1 + (4 * (N:ℝ))⁻¹) ^ (4 * N) ≤ (Real.sqrt (rho0R N 0)) ^ (4 * N) :=
    pow_le_pow_left₀ hb0 hbase (4 * N)
  have h2 : (2:ℝ) ≤ (Real.sqrt (rho0R N 0)) ^ (4 * N) := le_trans hbern hmono
  have hspos : (0:ℝ) < Real.sqrt (rho0R N 0) := Real.sqrt_pos.2 hrhpos
  have hppos : (0:ℝ) < (Real.sqrt (rho0R N 0)) ^ (4 * N) := pow_pos hspos _
  calc (Real.sqrt (rho0R N 0))⁻¹ ^ (4 * N)
      = ((Real.sqrt (rho0R N 0)) ^ (4 * N))⁻¹ := by rw [inv_pow]
    _ ≤ 2⁻¹ := (inv_le_inv₀ hppos (by norm_num)).mpr h2
    _ = 1 / 2 := by norm_num

/-- **The loop's fully explicit round count.**  In the central-cut regime (`ρmax = 0`, the case
`Aat_vol_below_central` isolates), both side conditions of the refuted verdict hold at the explicit
count `T₀ = simRounds n Φ₀ r (4·(n·n))`: `4N` rounds halve the contraction factor, and the
`Nat.clog 2` factor clears the potential ratio.  So `strictBody_refuted_prefix_concrete` can be run
at `m = 4·(n·n)`, `K = Nat.clog 2 ⌈2Φ₀/r^{n·n}⌉₊` with no search at all. -/
theorem central_run_budget {n : ℕ} (hn : 2 ≤ n) (M : ℚ) (hM : 0 < M) {δq cAq : ℚ}
    (hδq : 0 < δq) (hcAq : 0 ≤ cAq) :
    (Real.sqrt (rho0R (n * n) ((0 : ℚ) : ℝ)))⁻¹ ^ (4 * (n * n)) ≤ 1 / 2 ∧
      volPot (n * n) (initShapeOf (n * n) M)
        * (1 / 2) ^ (simRounds n (volPot (n * n) (initShapeOf (n * n) M))
            ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) (4 * (n * n))) <
        ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n) := by
  have hn' : 2 ≤ n * n := by nlinarith
  refine ⟨?_, ?_⟩
  · simpa using halving_time_explicit hn'
  · exact simRounds_budget (n := n) M hM hδq hcAq (m := 4 * (n * n)) (by omega)

end QMCLeafB.SimLoop

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.SimLoop.Aat_cast_posDef_prefix
#print axioms QMCLeafB.SimLoop.Prefix.strictBody_refuted_prefix_concrete
#print axioms QMCLeafB.SimLoop.simulate_sound
#print axioms QMCLeafB.SimLoop.simRounds_budget
#print axioms QMCLeafB.SimLoop.halving_time_explicit
#print axioms QMCLeafB.SimLoop.central_run_budget


