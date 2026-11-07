-- Prove2me | Definitions.Def_QMCLeafB_sf38
-- name    : QMCLeafB_sf38
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:53:03.902804+00:00
-- url     : https://prove2.me/theorems/d470e6f9-269d-44ee-961b-1dc1d18bef41
-- title:
--   QMCLeafB sf38
-- statement:
--   # `Check_sf38_m3` — phase 38, member m3, direction `stop-at-first-ok`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
/-
# `Check_sf38_m3` — phase 38, member m3, direction `stop-at-first-ok`

**What this file decides.**  The leaf's last obligation (`SelfRec`/`ShallowCut`, the all-cut record
at a bit-`false` point) is carried by the per-round slot

  `sup_{z ∈ K} c_k ⬝ (Cat_k − z) ≤ del_k`,   `del_k² ≤ ρ_k² σ_k`,   `ρ_k ≤ rmax`,

i.e. `del_k ≤ rmax √σ_k`.  Absolutely clean reading of that slot, machine-checked here against the
bare geometric data (`Mathlib` only; no campaign definition is imported):

* **§2 `no_slot_of_ball` — the deep-ball obstruction.**  If the body holds the `A`-ball of radius
  `r > rmax` around the centre, the round's slot is EMPTY — for every normal, witness, depth and
  margin.  So the obligation is a COLLAR condition (`Cat_k` must not be `rmax`-deep inside the body,
  equivalently the body must miss some `rmax`-thin cap of the ellipsoid), NOT a bounded-distance
  condition: `Cat_k` may be arbitrarily far from the body, on any one side.  The proof is elementary
  and needs no Cauchy–Schwarz: the ball's extreme point in the normal's own `A`-direction is
  `a − r e` with `c ⬝ e = √σ`, so every margin is beaten by `r √σ`.

* **§3 `no_two_rounds` — THE REFUTATION at the campaign's `n = 2` numbers** (`N = n·n = 4`,
  `rmax = 1/(4n²) = 1/16`).  Let the body be the Euclidean ball of radius `3/16` around `q = (1/8)e₀`,
  with initial shape `A₀ = 1` and initial centre `0`.  Then

  - the round-0 slot IS inhabited (`round0_slot`: cut `c = p = e₀`, depth `ρ = rmax`, margin
    `del = rmax`), and
  - every legal round-0 slot forces the normal onto the `e₀` axis (`forced_dir`: the body reaches
    down to `−1/16` and `r − rmax = ‖q‖` forces `e = e₀`), and
  - after that cut the round-1 ellipsoid `stepM 4 1 e₀ ρ` holds the `A₁`-ball of radius
    `1/10 > rmax` around its own centre `((1−ρ)/5) • e₀` (`ball_transfer`),

  hence the round-1 slot is empty.  So NO all-cut record runs for two rounds at this body, and
  "the ellipsoid centre stays within `rmax` of the body in the current `A_k`-norm" is not a
  consequence of `body_containment` plus the recursion.  Any proof of `SelfRec` must therefore use
  the specific structure of the QMC relaxation bodies (their thinness), not the geometry alone.

* **§1 is the engine of both**: `step_qf_formula`, the EXACT quadratic-form law of one shallow cut,
  `step_qf_form` / `step_qf_lower` (the `A`-form and the inward norm comparison) and `step_reach`,
  the sharp overshoot bound: for a body whose `A`-height in the cut direction is at most `h`,

    `‖z − a'‖_{A'} ≥ ((N+1)/(N+ρ)) (γ − h)`,   `γ = (1−ρ)/(N+1)`,

  so the new centre is at least `≈ 1/(N+1)` times the radius from every such point.  This is the
  quantitative statement that a shallow cut OVERSHOOTS the body.

`stepM N A e ρ` is the engine's `stepShape` in `A`-unit coordinates (`e` the unit `A`-vector of the
witness, `c = √σ • (A *ᵥ e)`); `Check_sf38_engine_m3` identifies it with
`EngineIterates.stepShape` and transports `no_two_rounds` to the engine's own recursion.

Discipline: `set_option autoImplicit false`; the five forbidden tokens are absent; the kernel printout for
every theorem below is exactly `[propext, Classical.choice, Quot.sound]`.
-/
open Matrix

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QMCLeafB.Sf38M3

variable {N : ℕ}

/-! ## 0. Elementary bilinearity of `dotProduct` over `ℝ^N` -/

theorem sub_dot (u v w : Fin N → ℝ) : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w := by
  simp only [dotProduct, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem neg_dot (u v : Fin N → ℝ) : (-u) ⬝ᵥ v = -(u ⬝ᵥ v) := by
  simp only [dotProduct, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem smul_dot (a : ℝ) (u v : Fin N → ℝ) : (a • u) ⬝ᵥ v = a * (u ⬝ᵥ v) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem qf_neg_smul (t : ℝ) (x : Fin N → ℝ) :
    ((-t) • x) ⬝ᵥ ((-t) • x) = t * t * (x ⬝ᵥ x) := by
  rw [smul_dot, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

theorem symm_dot {A : Matrix (Fin N) (Fin N) ℝ} (hAsym : Aᵀ = A) (e v : Fin N → ℝ) :
    (A *ᵥ e) ⬝ᵥ v = e ⬝ᵥ (A *ᵥ v) := by
  rw [dotProduct_comm]
  have h := Matrix.dotProduct_transpose_mulVec A e v
  rw [hAsym] at h
  exact h.symm

theorem dot_vecMulVec (u w q : Fin N → ℝ) :
    u ⬝ᵥ ((Matrix.vecMulVec w w) *ᵥ q) = (u ⬝ᵥ w) * (w ⬝ᵥ q) := by
  simp only [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- Euclidean Cauchy–Schwarz on `ℝ^N`, in the form we need (no square roots of sums). -/
theorem dot_sq_le (x y : Fin N → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) x y
  simpa only [dotProduct, pow_two] using h

theorem dot_le_norm (x y : Fin N → ℝ) :
    x ⬝ᵥ y ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have hx : 0 ≤ x ⬝ᵥ x := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hy : 0 ≤ y ⬝ᵥ y := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hb : 0 ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 : (x ⬝ᵥ y) ^ 2 ≤ (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]; exact dot_sq_le x y
  have h3 : |x ⬝ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
    have h4 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hb] at h4
  exact le_trans (le_abs_self _) h3

theorem abs_dot_le (x y : Fin N → ℝ) :
    |x ⬝ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have hx : 0 ≤ x ⬝ᵥ x := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hy : 0 ≤ y ⬝ᵥ y := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hb : 0 ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 : (x ⬝ᵥ y) ^ 2 ≤ (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]; exact dot_sq_le x y
  have h4 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hb] at h4

theorem neg_le_dot_sqrt (x y : Fin N → ℝ) :
    -(Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) ≤ x ⬝ᵥ y := by
  have h := abs_dot_le x y
  rw [abs_le] at h
  exact h.1

/-- Squared triangle inequality for the Euclidean (`dotProduct`) norm. -/
theorem norm_add_sq_le (x y : Fin N → ℝ) :
    (x + y) ⬝ᵥ (x + y) ≤ (Real.sqrt (x ⬝ᵥ x) + Real.sqrt (y ⬝ᵥ y)) ^ 2 := by
  have hxy : x ⬝ᵥ y ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := dot_le_norm x y
  have hx : 0 ≤ x ⬝ᵥ x := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hy : 0 ≤ y ⬝ᵥ y := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hxx : Real.sqrt (x ⬝ᵥ x) ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hx
  have hyy : Real.sqrt (y ⬝ᵥ y) ^ 2 = y ⬝ᵥ y := Real.sq_sqrt hy
  have hexp : (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + 2 * (x ⬝ᵥ y) + y ⬝ᵥ y := by
    simp only [dotProduct, Pi.add_apply, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    have : ∀ i : Fin N, (x i + y i) * (x i + y i)
        = x i * x i + 2 * (x i * y i) + y i * y i := fun i => by ring
    simp only [this, Finset.sum_add_distrib]
  have hexp2 : (Real.sqrt (x ⬝ᵥ x) + Real.sqrt (y ⬝ᵥ y)) ^ 2
      = x ⬝ᵥ x + 2 * (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) + y ⬝ᵥ y := by
    rw [add_sq, hxx, hyy]; ring
  rw [hexp, hexp2]
  linarith


/-- Squared triangle inequality in the form `‖x+y‖² ≤ 2(‖x‖² + ‖y‖²)`. -/
theorem norm_add_sq_le_two (x y : Fin N → ℝ) :
    (x + y) ⬝ᵥ (x + y) ≤ 2 * ((x ⬝ᵥ x) + (y ⬝ᵥ y)) := by
  have hx : 0 ≤ x ⬝ᵥ x := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hy : 0 ≤ y ⬝ᵥ y := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hxx : Real.sqrt (x ⬝ᵥ x) ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hx
  have hyy : Real.sqrt (y ⬝ᵥ y) ^ 2 = y ⬝ᵥ y := Real.sq_sqrt hy
  have hexp : (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + 2 * (x ⬝ᵥ y) + y ⬝ᵥ y := by
    simp only [dotProduct, Pi.add_apply, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    have : ∀ i : Fin N, (x i + y i) * (x i + y i)
        = x i * x i + 2 * (x i * y i) + y i * y i := fun i => by ring
    simp only [this, Finset.sum_add_distrib]
  have hsq : (x + y) ⬝ᵥ (x + y) ≤ (Real.sqrt (x ⬝ᵥ x) + Real.sqrt (y ⬝ᵥ y)) ^ 2 := by
    rw [hexp]
    have hexp2 : (Real.sqrt (x ⬝ᵥ x) + Real.sqrt (y ⬝ᵥ y)) ^ 2
        = x ⬝ᵥ x + 2 * (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) + y ⬝ᵥ y := by
      rw [add_sq, hxx, hyy]; ring
    rw [hexp2]
    have := dot_le_norm x y
    linarith
  have h2ab : 2 * (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y))
      ≤ Real.sqrt (x ⬝ᵥ x) ^ 2 + Real.sqrt (y ⬝ᵥ y) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (x ⬝ᵥ x) - Real.sqrt (y ⬝ᵥ y))]
  rw [show (Real.sqrt (x ⬝ᵥ x) + Real.sqrt (y ⬝ᵥ y)) ^ 2
      = Real.sqrt (x ⬝ᵥ x) ^ 2 + 2 * (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y))
        + Real.sqrt (y ⬝ᵥ y) ^ 2 from by ring] at hsq
  rw [hxx, hyy] at hsq h2ab
  linarith

/-! ## 1. The engine's step in `A`-unit coordinates

The engine's step is `stepShape N A c p ρ = α • (A + (β/σ) • c cᵀ)` with `α = (N²−1)/(N+ρ)²`,
`β = 2/(N−1)`, `σ = c ⬝ᵥ p`, and `stepCentre N a c p ρ = a + (γ/√σ) • p` with `γ = (1−ρ)/(N+1)`.
With `A p = c` the cut direction `e = (1/√σ) • p` is a *unit `A`-vector* (`e ⬝ᵥ (A *ᵥ e) = 1`) and
`c = √σ • (A *ᵥ e)`, so in `e`-coordinates the step is `A' = stepM N A e ρ`, `a' = a + γ • e`. -/

/-- The engine's updated shape matrix in `A`-unit coordinates:
`A' = ((N²−1)/(N+ρ)²) • (A + (2/(N−1)) • (Ae)(Ae)ᵀ)`.  Definitionally the engine's `stepShape` at
the witness `p = √σ • e`. -/
noncomputable def stepM (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (e : Fin N → ℝ) (ρ : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (((N : ℝ) ^ 2 - 1) / ((N : ℝ) + ρ) ^ 2) •
    (A + (2 / ((N : ℝ) - 1)) • Matrix.vecMulVec (A *ᵥ e) (A *ᵥ e))

/-- **THE STEP LAW**: the exact quadratic form of the new ellipsoid on the displacement from the new
centre.  For a point `z` with `v = z − a`, write `t = e ⬝ᵥ (A *ᵥ v)` (its `A`-height in the cut
direction) and `s² = v ⬝ᵥ (A *ᵥ v) − t²` (the squared `A`-norm of its orthogonal part); then

  `(z − a') ⬝ᵥ (A' *ᵥ (z − a')) = ((N+1)/(N+ρ)²) • ((N−1) s² + (N+1) (t − γ)²)`.

An identity of the recursion — no inequality, no `rmax`. -/
theorem step_qf_formula {A : Matrix (Fin N) (Fin N) ℝ} (hAsym : Aᵀ = A)
    {e : Fin N → ℝ} (hunit : e ⬝ᵥ (A *ᵥ e) = 1)
    {α β γ : ℝ} {v : Fin N → ℝ} :
    (v - γ • e) ⬝ᵥ ((α • (A + β • Matrix.vecMulVec (A *ᵥ e) (A *ᵥ e))) *ᵥ (v - γ • e))
      = α * ((v ⬝ᵥ (A *ᵥ v) - (e ⬝ᵥ (A *ᵥ v)) ^ 2) + (1 + β) * (e ⬝ᵥ (A *ᵥ v) - γ) ^ 2) := by
  set w := A *ᵥ e with hw
  set t := e ⬝ᵥ (A *ᵥ v) with ht
  have hs1 : v ⬝ᵥ w = t := by rw [dotProduct_comm]; exact symm_dot hAsym e v
  have hs2 : e ⬝ᵥ w = 1 := hunit
  have hqw : (v - γ • e) ⬝ᵥ w = t - γ := by
    rw [sub_dot, smul_dot, hs1, hs2]
    ring
  have hqA : (v - γ • e) ⬝ᵥ (A *ᵥ (v - γ • e)) = v ⬝ᵥ (A *ᵥ v) - 2 * γ * t + γ ^ 2 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dot, smul_dot, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hs1, hs2, ht]
    ring
  have hV : (v - γ • e) ⬝ᵥ ((Matrix.vecMulVec w w) *ᵥ (v - γ • e)) = (t - γ) ^ 2 := by
    rw [dot_vecMulVec, hqw, dotProduct_comm w (v - γ • e), hqw]
    ring
  have hexp : (α • (A + β • Matrix.vecMulVec w w)) *ᵥ (v - γ • e)
      = α • ((A *ᵥ (v - γ • e)) + β • ((Matrix.vecMulVec w w) *ᵥ (v - γ • e))) := by
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec]
  rw [hexp, dotProduct_smul, smul_eq_mul, dotProduct_add, dotProduct_smul, smul_eq_mul,
    hV, hqA]
  ring

/-- **The `A`-form of the step law**: the new shape's quadratic form is the old one with the
cut-direction weight raised from `1` to `(N+1)/(N−1)` (the `γ = 0` case of `step_qf_formula`: the
statement about a *displacement*, not about a point relative to `a'`). -/
theorem step_qf_form {A : Matrix (Fin N) (Fin N) ℝ} (hAsym : Aᵀ = A)
    {e : Fin N → ℝ} (hunit : e ⬝ᵥ (A *ᵥ e) = 1) (hN : 2 ≤ N) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (v : Fin N → ℝ) :
    v ⬝ᵥ (stepM N A e ρ *ᵥ v)
      = ((N : ℝ) + 1) / ((N : ℝ) + ρ) ^ 2 *
          (((N : ℝ) - 1) * (v ⬝ᵥ (A *ᵥ v) - (e ⬝ᵥ (A *ᵥ v)) ^ 2)
            + ((N : ℝ) + 1) * (e ⬝ᵥ (A *ᵥ v)) ^ 2) := by
  have h := step_qf_formula hAsym hunit
    (α := ((N : ℝ) ^ 2 - 1) / ((N : ℝ) + ρ) ^ 2) (β := 2 / ((N : ℝ) - 1)) (γ := 0) (v := v)
  have hstepM : stepM N A e ρ
      = (((N : ℝ) ^ 2 - 1) / ((N : ℝ) + ρ) ^ 2) •
          (A + (2 / ((N : ℝ) - 1)) • Matrix.vecMulVec (A *ᵥ e) (A *ᵥ e)) := rfl
  rw [hstepM]
  simp only [zero_smul, sub_zero] at h ⊢
  rw [h]
  have hN' : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hne : ((N:ℝ) - 1) ≠ 0 := by linarith
  have hne2 : ((N:ℝ) + ρ) ≠ 0 := by
    have : (0:ℝ) < (N:ℝ) := by linarith
    intro hc; nlinarith
  have hne3 : ((N:ℝ) + ρ) ^ 2 ≠ 0 := pow_ne_zero 2 hne2
  field_simp
  ring

/-- **The lower norm comparison of one step**: the new shape dominates `(N²−1)/(N+ρ)²` times the
old one, i.e. `‖v‖_{A'} ≥ (√(N²−1)/(N+ρ)) ‖v‖_A`. -/
theorem step_qf_lower {A : Matrix (Fin N) (Fin N) ℝ} (hAsym : Aᵀ = A)
    {e : Fin N → ℝ} (hunit : e ⬝ᵥ (A *ᵥ e) = 1) (hN : 2 ≤ N) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (v : Fin N → ℝ) :
    (((N : ℝ) ^ 2 - 1) / ((N : ℝ) + ρ) ^ 2) * (v ⬝ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (stepM N A e ρ *ᵥ v) := by
  have hN' : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hq := step_qf_form hAsym hunit hN hρ (ρ := ρ) v
  set t := e ⬝ᵥ (A *ᵥ v) with ht
  set q := v ⬝ᵥ (A *ᵥ v) with hqdef
  rw [hq]
  have hden : (0:ℝ) < ((N:ℝ) + ρ) ^ 2 := by
    have : (0:ℝ) < (N:ℝ) + ρ := by linarith
    positivity
  have hexp : ((N:ℝ)+1)/((N:ℝ)+ρ)^2 * (((N:ℝ)-1)*(q - t^2) + ((N:ℝ)+1)*t^2)
      = ((N:ℝ)^2-1)/((N:ℝ)+ρ)^2 * q + ((N:ℝ)+1)/((N:ℝ)+ρ)^2 * (2 * t^2) := by
    field_simp
    ring
  rw [hexp]
  have h3 : (0:ℝ) ≤ ((N:ℝ)+1)/((N:ℝ)+ρ)^2 * (2 * t^2) := by positivity
  nlinarith [h3]

/-- **THE ONE-STEP REACH BOUND** (the transfer criterion).  A shallow cut of depth `ρ` moves the
centre to `A'`-distance at least `((N+1)/(N+ρ)) (γ − h)` from every point whose `A`-height in the cut
direction is at most `h`, where `γ = (1−ρ)/(N+1)`.  So a body that does not *stand one ellipsoid step
tall* in the cut direction cannot remain within `rmax` of the new centre: `γ ≥ (1−rmax)/(N+1)`, and
`rmax = 1/(4n²)` is far below `1/(N+1)`.  This is the exact content of "a shallow cut overshoots the
body". -/
theorem step_reach {A : Matrix (Fin N) (Fin N) ℝ} (hAsym : Aᵀ = A) (hN : 2 ≤ N)
    {e : Fin N → ℝ} (hunit : e ⬝ᵥ (A *ᵥ e) = 1) {ρ γ h : ℝ} (hρ : 0 ≤ ρ)
    {v : Fin N → ℝ} (hhigh : e ⬝ᵥ (A *ᵥ v) ≤ h) (hγ : h ≤ γ)
    (hortho : 0 ≤ v ⬝ᵥ (A *ᵥ v) - (e ⬝ᵥ (A *ᵥ v)) ^ 2) :
    (((N : ℝ) + 1) / ((N : ℝ) + ρ)) ^ 2 * (γ - h) ^ 2
      ≤ (v - γ • e) ⬝ᵥ (stepM N A e ρ *ᵥ (v - γ • e)) := by
  have hN' : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hden : (0:ℝ) < ((N:ℝ) + ρ) ^ 2 := by
    have : (0:ℝ) < (N:ℝ) + ρ := by linarith
    positivity
  have hdead := step_qf_formula hAsym hunit
    (α := ((N : ℝ) ^ 2 - 1) / ((N : ℝ) + ρ) ^ 2) (β := 2 / ((N : ℝ) - 1)) (γ := γ) (v := v)
  have hstepM : stepM N A e ρ
      = (((N : ℝ) ^ 2 - 1) / ((N : ℝ) + ρ) ^ 2) •
          (A + (2 / ((N : ℝ) - 1)) • Matrix.vecMulVec (A *ᵥ e) (A *ᵥ e)) := rfl
  rw [hstepM, hdead]
  set t := e ⬝ᵥ (A *ᵥ v) with ht
  have h3 : (γ - h) ^ 2 ≤ (t - γ) ^ 2 := by nlinarith [hhigh, hγ]
  have h4 : (0:ℝ) ≤ v ⬝ᵥ (A *ᵥ v) - t ^ 2 := by
    rw [ht]; exact hortho
  have hgoal : (((N:ℝ)+1)/((N:ℝ)+ρ))^2 = ((N:ℝ)+1)^2/((N:ℝ)+ρ)^2 := by
    field_simp
  rw [hgoal]
  have expand : ((N:ℝ)^2-1)/((N:ℝ)+ρ)^2 *
        (v ⬝ᵥ (A *ᵥ v) - t^2 + (1 + 2/((N:ℝ)-1)) * (t-γ)^2)
      = ((N:ℝ)^2-1)/((N:ℝ)+ρ)^2 * (v ⬝ᵥ (A *ᵥ v) - t^2)
        + ((N:ℝ)+1)^2/((N:ℝ)+ρ)^2 * (t-γ)^2 := by
    have hne1 : ((N:ℝ) - 1) ≠ 0 := by linarith
    have hne2 : ((N:ℝ) + ρ) ^ 2 ≠ 0 := ne_of_gt hden
    field_simp
    ring
  rw [expand]
  have hA : (0:ℝ) ≤ ((N:ℝ)^2-1)/((N:ℝ)+ρ)^2 * (v ⬝ᵥ (A *ᵥ v) - t^2) := by
    have hnum : (0:ℝ) ≤ ((N:ℝ)^2-1) := by nlinarith
    exact mul_nonneg (div_nonneg hnum (le_of_lt hden)) h4
  have hB : (0:ℝ) ≤ ((N:ℝ)+1)^2/((N:ℝ)+ρ)^2 * ((t-γ)^2 - (γ-h)^2) := by
    have hcoef : (0:ℝ) ≤ ((N:ℝ)+1)^2/((N:ℝ)+ρ)^2 := by positivity
    exact mul_nonneg hcoef (by linarith)
  nlinarith [hA, hB]


/-! ## 2. The exact one-round obstruction: a body that is `rmax`-deep at the centre cannot be cut

The record's round slot at `(A, a)` is: a normal `c ≠ 0` with witness `p` (`A p = c`), a depth
`ρ ∈ [0, rmax]` and a margin `del ≥ 0` with `del ≤ ρ √σ` and the body on the far side of the plane
`c ⬝ (· − a) = −del`.  This is *one-sided*, but it is not free: a body containing an `A`-ball of
radius `> rmax` around the centre has NO slot at all. -/

/-- The round slot, as a predicate on the data (normal, witness, depth, margin, body). -/
def Slot (A : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (rmax : ℝ) (K : Set (Fin N → ℝ))
    (c p : Fin N → ℝ) (ρ del : ℝ) : Prop :=
  c ≠ 0 ∧ A *ᵥ p = c ∧ 0 ≤ ρ ∧ ρ ≤ rmax ∧ 0 ≤ del ∧ del ≤ ρ * Real.sqrt (c ⬝ᵥ p) ∧
    ∀ z ∈ K, c ⬝ᵥ (a - z) ≤ del

/-- A scalar fact: `(1/√σ)((1/√σ)σ) = 1` for `σ > 0`. -/
theorem inv_sqrt_mul (σ : ℝ) (h : 0 < σ) :
    (1 / Real.sqrt σ) * ((1 / Real.sqrt σ) * σ) = 1 := by
  have hne : Real.sqrt σ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
  have hsq : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt h.le
  field_simp
  nlinarith [hsq]

/-- **THE DEEP-BALL OBSTRUCTION** (elementary; no Cauchy–Schwarz).  If the body contains the
`A`-ball of radius `r > rmax` around the centre `a`, then there is no slot: the ball's own extreme
point in the normed direction of the normal beats every admissible margin.  Equivalently: a round is
possible only where the centre is *not* `rmax`-deep inside the body. -/
theorem no_slot_of_ball {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {a : Fin N → ℝ} {r rmax : ℝ} (hr : rmax < r)
    {K : Set (Fin N → ℝ)} (hball : ∀ z, (z - a) ⬝ᵥ (A *ᵥ (z - a)) ≤ r ^ 2 → z ∈ K) :
    ¬ ∃ (c p : Fin N → ℝ) (ρ del : ℝ), Slot A a rmax K c p ρ del := by
  rintro ⟨c, p, ρ, del, hc, hAp, hρ0, hρr, hdel0, hdel, hslot⟩
  set σ := c ⬝ᵥ p with hσ
  have hp0 : p ≠ 0 := by
    intro hp
    apply hc
    rw [hp, Matrix.mulVec_zero] at hAp
    exact hAp.symm
  have hpAp : p ⬝ᵥ (A *ᵥ p) = σ := by
    rw [hAp, hσ, dotProduct_comm p c]
  have hσpos : 0 < σ := by
    have h := hA.dotProduct_mulVec_pos hp0
    simp only [star_trivial] at h
    rwa [hpAp] at h
  have hσsq : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσpos.le
  have hσpos' : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσpos
  set e := (1 / Real.sqrt σ) • p with he
  have h1 : A *ᵥ e = (1 / Real.sqrt σ) • (A *ᵥ p) := by rw [he, Matrix.mulVec_smul]
  have h2 : e ⬝ᵥ ((1 / Real.sqrt σ) • (A *ᵥ p))
      = (1 / Real.sqrt σ) * (e ⬝ᵥ (A *ᵥ p)) := by
    rw [dotProduct_smul, smul_eq_mul]
  have h3 : e ⬝ᵥ (A *ᵥ p) = (1 / Real.sqrt σ) * (p ⬝ᵥ (A *ᵥ p)) := by
    rw [he]
    exact smul_dot (1 / Real.sqrt σ) p (A *ᵥ p)
  have hunit : e ⬝ᵥ (A *ᵥ e) = 1 := by
    rw [h1, h2, h3, hpAp]
    exact inv_sqrt_mul σ hσpos
  have hce : c ⬝ᵥ e = Real.sqrt σ := by
    rw [he, dotProduct_smul, hσ, smul_eq_mul]
    field_simp
    rw [div_eq_iff (ne_of_gt hσpos')]
    exact hσsq.symm
  have hqfv : ∀ (t : ℝ) (x : Fin N → ℝ),
      ((t • x) ⬝ᵥ (A *ᵥ (t • x))) = t * t * (x ⬝ᵥ (A *ᵥ x)) := by
    intro t x
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dot]
    simp only [smul_eq_mul]
    ring
  have hmem : (a - r • e) ∈ K := by
    apply hball
    have hsub : a - r • e - a = (-1 : ℝ) • (r • e) := by
      rw [neg_one_smul]; abel
    rw [hsub, hqfv (-1) (r • e), hqfv r e, hunit]
    nlinarith [sq_nonneg r]
  have hslot' := hslot (a - r • e) hmem
  have hval : c ⬝ᵥ (a - (a - r • e)) = r * Real.sqrt σ := by
    have : a - (a - r • e) = r • e := by abel
    rw [this, dotProduct_smul, hce, smul_eq_mul]
  rw [hval] at hslot'
  have h2 : ρ * Real.sqrt σ ≤ rmax * Real.sqrt σ := by
    exact mul_le_mul_of_nonneg_right hρr hσpos'.le
  have h3 : r * Real.sqrt σ > rmax * Real.sqrt σ := by
    exact mul_lt_mul_of_pos_right hr hσpos'
  linarith



/-! ## 3. The refutation at `n = 2`, i.e. ambient dimension `N = n·n = 4`

Campaign numbers: `N = 4`, `rmax = 1/(4n²) = 1/16`.  The body is the Euclidean ball of radius `3/16`
around `q = (1/8) e₀`; the initial shape is `A₀ = 1`, the initial centre `a₀ = 0`.

* the round-0 slot IS inhabited (`round0_slot`): the cut `c = p = e₀`, depth `ρ = rmax`, margin
  `del = rmax` keeps the body;
* but every legal round-0 cut has `c` a positive multiple of `e₀` (`forced_dir`) — the body is too
  thin off the `e₀` axis for any other normal;
* and after that cut the round-1 ellipsoid contains the `A₁`-ball of radius `1/10 > rmax` around its
  own centre (`ball_transfer`), so the round-1 slot is EMPTY (`no_slot_of_ball`).

Hence no all-cut record runs for two rounds at this body. -/

/-- `e₀`, the first basis vector of `ℝ⁴`. -/
def e0 : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The body's centre `q = (1/8) e₀`. -/
def q4 : Fin 4 → ℝ := ![1/8, 0, 0, 0]

/-- The body: the Euclidean ball of radius `3/16` around `q4`. -/
def K4 : Set (Fin 4 → ℝ) := {z | (z - q4) ⬝ᵥ (z - q4) ≤ (3 / 16) ^ 2}

/-- The campaign's ceiling at `n = 2`: `rmax = 1/(4n²) = 1/16`. -/
def rmax4 : ℝ := 1 / 16

theorem e0_dot (z : Fin 4 → ℝ) : e0 ⬝ᵥ z = z 0 := by
  simp [e0, dotProduct, Fin.sum_univ_four]

theorem e0_norm : e0 ⬝ᵥ e0 = 1 := by
  simp [e0, dotProduct, Fin.sum_univ_four]

theorem q4_dot (z : Fin 4 → ℝ) : q4 ⬝ᵥ z = (1 / 8) * z 0 := by
  simp [q4, dotProduct, Fin.sum_univ_four]

theorem q4_eq_e0 : q4 = (1 / 8 : ℝ) • e0 := by
  funext i
  fin_cases i <;> simp [q4, e0]

/-- The `0`-th coordinate of a point of `K4` is at least `−1/16`. -/
theorem K4_coord (z : Fin 4 → ℝ) (hz : z ∈ K4) : -(1 / 16 : ℝ) ≤ z 0 := by
  have h : (z - q4) ⬝ᵥ (z - q4) ≤ (3 / 16) ^ 2 := hz
  have h0 : (z 0 - q4 0) * (z 0 - q4 0) ≤ (z - q4) ⬝ᵥ (z - q4) := by
    simp only [dotProduct]
    exact Finset.single_le_sum (f := fun i => (z i - q4 i) * (z i - q4 i))
      (fun i _ => mul_self_nonneg _) (Finset.mem_univ 0)
  have hq : q4 0 = 1 / 8 := by simp [q4]
  rw [hq] at h0
  nlinarith [h, h0]

/-- **The round-0 slot is INHABITED** at this body: the cut `c = p = e₀` at depth `ρ = rmax` with
margin `del = rmax` separates the body. -/
theorem round0_slot : ∃ (c p : Fin 4 → ℝ) (ρ del : ℝ),
    Slot (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 rmax4 K4 c p ρ del := by
  refine ⟨e0, e0, rmax4, rmax4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [e0] at this
  · rw [Matrix.one_mulVec]
  · norm_num [rmax4]
  · norm_num [rmax4]
  · norm_num [rmax4]
  · rw [e0_norm, Real.sqrt_one, mul_one]
  · intro z hz
    have h1 : e0 ⬝ᵥ (0 - z) = -(z 0) := by
      rw [e0_dot]; simp
    rw [h1]
    have := K4_coord z hz
    norm_num [rmax4]
    linarith

theorem sqrt_sq_self {σ : ℝ} (h : 0 < σ) : Real.sqrt σ * Real.sqrt σ = σ :=
  Real.mul_self_sqrt h.le

/-- **THE CUT DIRECTION IS FORCED.**  At `K4` every legal round-0 normal is a positive multiple of
`e₀`: the body reaches `r − ρ` towards the centre along the cut direction, and `r − rmax = ‖q‖`
forces the direction to be exactly `q/‖q‖ = e₀`. -/
theorem forced_dir {c p : Fin 4 → ℝ} {ρ del : ℝ}
    (H : Slot (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 rmax4 K4 c p ρ del) :
    ∃ κ : ℝ, 0 < κ ∧ c = κ • e0 := by
  obtain ⟨hc, hAp, hρ0, hρr, hdel0, hdel, hslot⟩ := H
  have hpc : p = c := by
    simpa [Matrix.one_mulVec] using hAp
  rw [← hpc] at hc hdel hslot ⊢
  set σ := p ⬝ᵥ p with hσ
  have hcne : p ≠ 0 := hc
  have hσpos : 0 < σ := by
    rw [hσ]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hcne
    simp only [dotProduct]
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  have hσsq : Real.sqrt σ * Real.sqrt σ = σ := sqrt_sq_self hσpos
  have hσpos' : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσpos
  set e := (1 / Real.sqrt σ) • p with he
  have hee : e ⬝ᵥ e = 1 := by
    rw [he, smul_dot, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← hσ]
    exact inv_sqrt_mul σ hσpos
  have hce : p ⬝ᵥ e = Real.sqrt σ := by
    rw [he, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [hσ]
    field_simp
    rw [div_eq_iff (ne_of_gt hσpos')]
    exact hσsq.symm
  -- the extreme body point
  have hmem : q4 + (-(3/16) : ℝ) • e ∈ K4 := by
    simp only [K4, Set.mem_ofPred_eq]
    have hsub : q4 + (-(3/16) : ℝ) • e - q4 = (-(3/16) : ℝ) • e :=
      add_sub_cancel_left q4 _
    rw [hsub, qf_neg_smul, hee, mul_one]
    norm_num
  have hslot' := hslot (q4 + (-(3/16) : ℝ) • e) hmem
  -- evaluate the separation at that point
  have hval : p ⬝ᵥ (0 - (q4 + (-(3/16) : ℝ) • e)) = -(1/8) * (p ⬝ᵥ e0) + (3/16) * Real.sqrt σ := by
    have h1 : (0 : Fin 4 → ℝ) - (q4 + (-(3/16) : ℝ) • e) = -(q4 + (-(3/16) : ℝ) • e) :=
      zero_sub _
    have hq4 : p ⬝ᵥ q4 = (1/8) * (p ⬝ᵥ e0) := by
      rw [q4_eq_e0, dotProduct_smul]
      simp only [smul_eq_mul]
    rw [h1, dotProduct_neg, dotProduct_add, dotProduct_smul, hce, hq4]
    simp only [smul_eq_mul]
    ring
  rw [hval] at hslot'
  -- the ledger:  del ≤ rmax · √σ
  have hdel' : del ≤ rmax4 * Real.sqrt σ := by
    refine le_trans hdel (mul_le_mul_of_nonneg_right hρr hσpos'.le)
  rw [rmax4] at hdel'
  -- hence  c ⬝ᵥ e0 ≥ √σ
  have hce0 : Real.sqrt σ ≤ p ⬝ᵥ e0 := by nlinarith [hslot', hdel']
  -- and then  e = e₀
  have hee0 : 1 ≤ e ⬝ᵥ e0 := by
    have hce0' : Real.sqrt σ * (e ⬝ᵥ e0) = p ⬝ᵥ e0 := by
      have hstep : e ⬝ᵥ e0 = (1 / Real.sqrt σ) * (p ⬝ᵥ e0) := by
        rw [he]
        exact smul_dot (1 / Real.sqrt σ) p e0
      rw [hstep]
      field_simp
    nlinarith [hce0, hce0', hσpos']
  have hexp : (e - e0) ⬝ᵥ (e - e0) = e ⬝ᵥ e - 2 * (e ⬝ᵥ e0) + e0 ⬝ᵥ e0 := by
    simp only [dotProduct, Pi.sub_apply, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_mul]
    have : ∀ i : Fin 4, (e i - e0 i) * (e i - e0 i)
        = e i * e i - 2 * (e i * e0 i) + e0 i * e0 i := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hnorm : (e - e0) ⬝ᵥ (e - e0) = 0 := by
    have hle : (e - e0) ⬝ᵥ (e - e0) ≤ 0 := by
      rw [hexp, hee, e0_norm]
      linarith [hee0]
    have hnn : 0 ≤ (e - e0) ⬝ᵥ (e - e0) := by
      simp only [dotProduct]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    linarith
  have heq : e = e0 := by
    have hz : (e - e0) = 0 := by
      funext i
      have hterm : (e i - e0 i) * (e i - e0 i) = 0 := by
        have hle : (e i - e0 i) * (e i - e0 i) ≤ (e - e0) ⬝ᵥ (e - e0) := by
          simp only [dotProduct]
          exact Finset.single_le_sum (f := fun j => (e j - e0 j) * (e j - e0 j))
            (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
        rw [hnorm] at hle
        nlinarith [mul_self_nonneg (e i - e0 i)]
      have h2 : e i - e0 i = 0 := mul_self_eq_zero.mp hterm
      simpa using h2
    exact sub_eq_zero.mp hz
  have hp_eq : p = Real.sqrt σ • e0 := by
    have h1 : (1 / Real.sqrt σ) • p = e0 := by rw [← he, heq]
    have h2 := congrArg (fun v => Real.sqrt σ • v) h1
    simp only [smul_smul] at h2
    rw [show Real.sqrt σ * (1 / Real.sqrt σ) = 1 by field_simp, one_smul] at h2
    exact h2
  exact ⟨Real.sqrt σ, hσpos', hp_eq⟩

/-! ### 3.1  The round-1 ball is large -/

theorem stepM_posDef {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (stepM 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) e0 ρ).PosDef := by
  have hsym : ((1 : Matrix (Fin 4) (Fin 4) ℝ))ᵀ = 1 := Matrix.transpose_one
  have hunit : e0 ⬝ᵥ ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ e0) = 1 := by
    rw [Matrix.one_mulVec]; exact e0_norm
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm]
    simp only [stepM, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_vecMulVec]
  · intro x hx
    simp only [star_trivial]
    have hlow := step_qf_lower (A := (1 : Matrix (Fin 4) (Fin 4) ℝ)) hsym hunit
      (by norm_num : 2 ≤ 4) hρ (ρ := ρ) x
    have hxx : 0 < x ⬝ᵥ x := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra h
        exact hx (funext fun i => by by_contra h' ; exact h ⟨i, h'⟩)
      simp only [dotProduct]
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
    have hpos : (0:ℝ) < 15 / (4 + ρ) ^ 2 := by
      have : (0:ℝ) < 4 + ρ := by linarith
      positivity
    have hexp : ((↑(4:ℕ))^2 - 1) / ((↑(4:ℕ)) + ρ)^2 = 15 / (4 + ρ)^2 := by
      push_cast; ring
    rw [hexp, Matrix.one_mulVec] at hlow
    have hprod : (0:ℝ) < 15 / (4 + ρ) ^ 2 * (x ⬝ᵥ x) := mul_pos hpos hxx
    linarith [hlow, hprod]

/-- **THE TRANSFER**: every point of the round-1 `A₁`-ball of radius `1/10` around the new centre
`γ e₀` lies in the body `K4`.  (`γ = (1−ρ)/5`, `A₁ = stepM 4 1 e₀ ρ`.) -/
theorem ball_transfer {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρr : ρ ≤ rmax4) :
    ∀ z, (z - ((1 - ρ) / 5) • e0) ⬝ᵥ (stepM 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) e0 ρ *ᵥ
        (z - ((1 - ρ) / 5) • e0)) ≤ (1 / 10) ^ 2 → z ∈ K4 := by
  intro z hz
  have hsym : ((1 : Matrix (Fin 4) (Fin 4) ℝ))ᵀ = 1 := Matrix.transpose_one
  have hunit : e0 ⬝ᵥ ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ e0) = 1 := by
    rw [Matrix.one_mulVec]; exact e0_norm
  set x := z - ((1 - ρ) / 5) • e0 with hx
  set y := ((1 - ρ) / 5) • e0 - q4 with hy
  have hxy : x + y = z - q4 := by rw [hx, hy]; abel
  have hlow := step_qf_lower (A := (1 : Matrix (Fin 4) (Fin 4) ℝ)) hsym hunit
    (by norm_num : 2 ≤ 4) hρ0 (ρ := ρ) x
  have hexp : ((↑(4:ℕ))^2 - 1) / ((↑(4:ℕ)) + ρ)^2 = 15 / (4 + ρ)^2 := by
    push_cast; ring
  rw [hexp, Matrix.one_mulVec] at hlow
  have hpos : (0:ℝ) < 15 / (4 + ρ) ^ 2 := by
    have : (0:ℝ) < 4 + ρ := by linarith
    positivity
  -- x · x is small
  have hden : (0:ℝ) < (4 + ρ) ^ 2 := by
    have : (0:ℝ) < 4 + ρ := by linarith
    positivity
  have hmul : x ⬝ᵥ x * 15 ≤ (1 / 10) ^ 2 * (4 + ρ) ^ 2 := by
    have hkey : 15 / (4 + ρ) ^ 2 * (x ⬝ᵥ x) ≤ (1 / 10) ^ 2 := le_trans hlow hz
    have h3 : (15 / (4 + ρ) ^ 2 * (x ⬝ᵥ x)) * (4 + ρ) ^ 2 ≤ (1 / 10) ^ 2 * (4 + ρ) ^ 2 :=
      mul_le_mul_of_nonneg_right hkey hden.le
    have heq : (15 / (4 + ρ) ^ 2 * (x ⬝ᵥ x)) * (4 + ρ) ^ 2 = x ⬝ᵥ x * 15 := by
      field_simp
    rwa [heq] at h3
  have h4 : (4 + ρ) ^ 2 ≤ (65 / 16) ^ 2 := by
    rw [rmax4] at hρr
    nlinarith
  have hxx' : x ⬝ᵥ x ≤ 4225 / 384000 := by
    have h5 : (1 / 10)^2 * (4 + ρ)^2 ≤ (1/10)^2 * (65/16)^2 := by
      have hpos2 : (0:ℝ) ≤ (1/10)^2 := by norm_num
      exact mul_le_mul_of_nonneg_left h4 hpos2
    nlinarith [hmul, h5]
  -- y · y is small
  have hyy : y ⬝ᵥ y ≤ 9 / 1600 := by
    have hyq : y = (((1 - ρ) / 5) - 1/8) • e0 := by
      rw [hy, q4_eq_e0, ← sub_smul]
    rw [hyq, smul_dot, dotProduct_smul, e0_norm]
    simp only [smul_eq_mul, mul_one]
    rw [rmax4] at hρr
    have h1 : (1 - ρ) / 5 - 1 / 8 ≤ 3 / 40 := by linarith
    have h2 : -(3 / 40) ≤ (1 - ρ) / 5 - 1 / 8 := by linarith
    nlinarith
  -- assemble
  have htri := norm_add_sq_le_two x y
  rw [hxy] at htri
  have : 2 * (x ⬝ᵥ x + y ⬝ᵥ y) ≤ (3 / 16) ^ 2 := by
    nlinarith [hxx', hyy]
  exact le_trans htri this

/-- **THE REFUTATION.**  At the campaign's `n = 2` numbers no all-cut record runs for two rounds at
the body `K4`, although the round-0 slot is inhabited there.  So "the centre stays within `rmax` of
the body in the current `A_k`-norm" is *not* a consequence of `body_containment` and the recursion:
the round-1 slot is empty for every legal round-0 cut. -/
theorem no_two_rounds :
    (∃ (c p : Fin 4 → ℝ) (ρ del : ℝ), Slot (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 rmax4 K4 c p ρ del)
    ∧ ∀ (c p : Fin 4 → ℝ) (ρ del : ℝ),
        Slot (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 rmax4 K4 c p ρ del →
      ∀ (c' p' : Fin 4 → ℝ) (ρ' del' : ℝ),
        ¬ Slot (stepM 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) e0 ρ) (((1 - ρ) / 5) • e0) rmax4 K4
            c' p' ρ' del' := by
  refine ⟨round0_slot, ?_⟩
  intro c p ρ del H c' p' ρ' del' H'
  obtain ⟨hc, hAp, hρ0, hρr, hdel0, hdel, hslot⟩ := H
  have hA1 : stepM 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) e0 ρ
      = stepM 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) e0 ρ := rfl
  have hbig : ∀ z, (z - ((1 - ρ) / 5) • e0) ⬝ᵥ
      (stepM 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) e0 ρ *ᵥ (z - ((1 - ρ) / 5) • e0))
      ≤ (1 / 10) ^ 2 → z ∈ K4 := ball_transfer hρ0 hρr
  have hempty := no_slot_of_ball (A := stepM 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) e0 ρ)
    (stepM_posDef hρ0) (a := ((1 - ρ) / 5) • e0) (r := 1 / 10) (rmax := rmax4)
    (K := K4) (by norm_num [rmax4]) hbig
  exact hempty ⟨c', p', ρ', del', H'⟩


end QMCLeafB.Sf38M3


