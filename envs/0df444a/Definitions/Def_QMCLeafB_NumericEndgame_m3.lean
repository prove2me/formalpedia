-- Prove2me | Definitions.Def_QMCLeafB_NumericEndgame_m3
-- name    : QMCLeafB_NumericEndgame_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:03:40.139711+00:00
-- url     : https://prove2.me/theorems/aa69eb3a-198a-40a8-918e-13334cd09075
-- title:
--   QMCLeafB NumericEndgame_m3
-- statement:
--   # Leaf-B phase 4 — the numeric endgame of the threshold engine (member m3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_EngineIterates
import Definitions.Def_QMCLeafB_EllipsoidVolume
/-
# Leaf-B phase 4 — the numeric endgame of the threshold engine (member m3)

This file supplies the *closed arithmetic and inequality* end of the ellipsoid engine: the step
that turns the geometry of the feasible body into a number that the runtime termination test
compares against `EngineIterates.volPot`.  It is the seam between

* `brick-ball-floor`:  a positive-margin body contains the Euclidean ball `eucBallAt a r`
  (radius `r > 0` explicit in the margin data), and
* `brick-answer-producer`: the *refuted-body* branch, i.e. the decision that the threshold body is
  empty once the loop's potential is below the floor.

The brief calls the floor `r^{2d}·det A ≤ 1`.  That is a two-line consequence of the eigenvalue
bound `A ⪯ r^{-2}·1`, which is what this file proves — over `ℝ`, with no measure theory, so it
does not depend on the ellipsoid-volume route of `Solutions/Check_EllipsoidVolume.lean`
(which proves the same floor for *Gram-parametrised* ellipsoids `E(B,c)`).

## The chain

| statement | what it says |
|---|---|
| `ray_le_of_ball` | ball ⇒ ray bound: `∀ v, vᵀv ≤ r² → vᵀAv ≤ 1` gives `vᵀAv ≤ r^{-2}·vᵀv` for *all* `v` |
| `eigen_le_of_unit` | hence the Rayleigh quotient at a unit vector is at most `r^{-2}` |
| `eigen_le` | hence every eigenvalue of a positive definite `A` is at most `r^{-2}` |
| `det_mul_pow_le_one` | hence `r^(2n)·det A ≤ 1` — the floor of the brief, in `det` form |
| `volPot_ge` | in the engine's own potential: `r^n ≤ volPot n A`, i.e. `Φ ≥ r^n` |
| `body_empty_of_floor` | `Φ ≤ ε < r^n` and the body inside the terminal ellipsoid ⇒ the body is empty |
| `body_empty_of_eucBallAt` | the same with the hypothesis in `EllipsoidVolume.eucBallAt` form |
| `empty_of_terminal` | the engine-shaped form: instantiated at `Aq = Aat n A0 cd K`, `a = Cat n a0 cd K` |

The last one is exactly the contract `brick-answer-producer` needs on its refutation branch: the
run length `K` and the containment come from `EngineIterates.engine_run`, the ball from
`brick-ball-floor`, and the contradiction `r^n ≤ Φ_K ≤ ε < r^n` from this file.

## The constant ledger

`thirteen_calls`, `gap_le_slack`, `v_split`, `eps_half` record the campaign's load-bearing closed
computations (bisection width `V/32768 ≤ V/20000`, `V = 2W`, the halved target `ε`), each by
`norm_num`/`linarith` only, so that no brick has to re-derive them by hand.

No `sorry`, no `axiom`; the axiom audit is at the end of the file.
-/

open Matrix
open scoped BigOperators

namespace QMCLeafB.NumericEndgame

variable {n : ℕ}

/-! ## 1.  Dot-product facts (the Euclidean structure, without a norm instance) -/

/-- `v ⬝ᵥ v ≥ 0`. -/
theorem dot_self_nonneg (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- A nonzero vector has strictly positive self dot product. -/
theorem dot_self_pos {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  rcases lt_or_eq_of_le (dot_self_nonneg v) with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv

/-- Scaling a vector scales the self dot product by the square of the factor. -/
theorem smul_dot_self (t : ℝ) (v : Fin n → ℝ) :
    (t • v) ⬝ᵥ (t • v) = t ^ 2 * (v ⬝ᵥ v) := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- Scaling the vector scales the quadratic form by the square of the factor. -/
theorem smul_qf (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (v : Fin n → ℝ) :
    (t • v) ⬝ᵥ (A *ᵥ (t • v)) = t ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-! ## 2.  From a contained ball to the ray bound -/

/-- **Ball ⇒ ray bound.**  If the quadratic form of `A` is at most `1` on the ball of radius
`r > 0` around the origin, then it is at most `r^{-2}·‖v‖²` everywhere: scale any `v` down onto the
sphere, where the hypothesis applies.  This is the only place the scaling argument is used. -/
theorem ray_le_of_ball {A : Matrix (Fin n) (Fin n) ℝ} {r : ℝ} (hr : 0 < r)
    (hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 → v ⬝ᵥ (A *ᵥ v) ≤ 1)
    (v : Fin n → ℝ) :
    v ⬝ᵥ (A *ᵥ v) ≤ (1 / r ^ 2) * (v ⬝ᵥ v) := by
  by_cases hv : v = 0
  · subst hv
    simp
  · have hvpos : 0 < v ⬝ᵥ v := dot_self_pos hv
    set s : ℝ := r / Real.sqrt (v ⬝ᵥ v)
    have hsq : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hvpos.le
    have hs2 : s ^ 2 = r ^ 2 / (v ⬝ᵥ v) := by
      rw [div_pow, hsq]
    have hmem : (s • v) ⬝ᵥ (s • v) = r ^ 2 := by
      rw [smul_dot_self, hs2]
      field_simp
    have hstep : s ^ 2 * (v ⬝ᵥ (A *ᵥ v)) ≤ 1 := by
      have h := hsub (s • v) (le_of_eq hmem)
      rwa [smul_qf] at h
    have hr2 : (0:ℝ) < r ^ 2 := by positivity
    have hdiv : (r ^ 2) * (v ⬝ᵥ (A *ᵥ v)) / (v ⬝ᵥ v) ≤ 1 := by
      have hre : (r ^ 2) * (v ⬝ᵥ (A *ᵥ v)) / (v ⬝ᵥ v)
          = (r ^ 2 / (v ⬝ᵥ v)) * (v ⬝ᵥ (A *ᵥ v)) := by field_simp
      rw [hre, ← hs2]
      exact hstep
    have h3 : (r ^ 2) * (v ⬝ᵥ (A *ᵥ v)) ≤ 1 * (v ⬝ᵥ v) :=
      (div_le_iff₀ hvpos).mp hdiv
    rw [one_mul] at h3
    have h4 : (r ^ 2)⁻¹ * ((r ^ 2) * (v ⬝ᵥ (A *ᵥ v))) ≤ (r ^ 2)⁻¹ * (v ⬝ᵥ v) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr2), one_mul] at h4
    have hgoal : (1 / r ^ 2) * (v ⬝ᵥ v) = (r ^ 2)⁻¹ * (v ⬝ᵥ v) := by rw [one_div]
    rw [hgoal]
    exact h4

/-! ## 2'.  The offset: a ball *anywhere* inside the ellipsoid

`engine_run` contains the body in `Ell (Aat K) (Cat K)`, whose centre `Cat K` moves with the run,
while the positive-margin ball coming from the separation oracle sits at a *fixed* point `b`.
So the floor has to be available with the ball and the ellipsoid centre separated; testing the
containment at `b ± v` cancels the linear term and gives the same bound. -/

/-- Expansion of the quadratic form at a sum (no symmetry of `A` needed). -/
theorem qf_add_expand (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    (x + y) ⬝ᵥ (A *ᵥ (x + y))
      = x ⬝ᵥ (A *ᵥ x) + x ⬝ᵥ (A *ᵥ y) + y ⬝ᵥ (A *ᵥ x) + y ⬝ᵥ (A *ᵥ y) := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  ring

/-- **A contained ball bounds the form at the centre**, wherever on the ball's centre sits: applying
the containment to `b + v` and to `b - v` and adding kills the two cross terms. -/
theorem ray_le_of_ball_offset {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {a b : Fin n → ℝ} {r : ℝ}
    (hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 → (b + v - a) ⬝ᵥ (A *ᵥ (b + v - a)) ≤ 1)
    {v : Fin n → ℝ} (hv : v ⬝ᵥ v ≤ r ^ 2) :
    v ⬝ᵥ (A *ᵥ v) ≤ 1 := by
  set z : Fin n → ℝ := b - a with hz
  have h1 : (z + v) ⬝ᵥ (A *ᵥ (z + v)) ≤ 1 := by
    have h := hsub v hv
    have e : b + v - a = z + v := by rw [hz]; abel
    rwa [e] at h
  have h2 : (z + -v) ⬝ᵥ (A *ᵥ (z + -v)) ≤ 1 := by
    have h := hsub (-v) (by simpa using hv)
    have e : b + (-v) - a = z + -v := by rw [hz]; abel
    rw [e] at h
    exact h
  rw [qf_add_expand] at h1
  rw [qf_add_expand] at h2
  simp only [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg] at h2
  have hz0 : 0 ≤ z ⬝ᵥ (A *ᵥ z) := hA.dotProduct_mulVec_nonneg z
  nlinarith

/-! ## 3.  The determinant floor -/

/-- **The Rayleigh quotient at a unit vector**: testing the ray bound on a unit eigenvector with
eigenvalue `λ` gives `λ ≤ r^{-2}`. -/
theorem eigen_le_of_unit {A : Matrix (Fin n) (Fin n) ℝ} {r : ℝ} (hr : 0 < r)
    (hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 → v ⬝ᵥ (A *ᵥ v) ≤ 1)
    {u : Fin n → ℝ} (hu : u ⬝ᵥ u = 1) {lam : ℝ} (hAu : A *ᵥ u = lam • u) :
    lam ≤ (r ^ 2)⁻¹ := by
  have hratio := ray_le_of_ball hr hsub u
  rw [hAu, dotProduct_smul, smul_eq_mul, hu, mul_one, one_div, mul_one] at hratio
  exact hratio

/-- **Every eigenvalue is at most `r^{-2}`.** -/
theorem eigen_le [DecidableEq (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {r : ℝ}
    (hr : 0 < r) (hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 → v ⬝ᵥ (A *ᵥ v) ≤ 1) (i : Fin n) :
    hA.isHermitian.eigenvalues i ≤ (r ^ 2)⁻¹ := by
  have hnorm : ‖hA.isHermitian.eigenvectorBasis i‖ = 1 :=
    hA.isHermitian.eigenvectorBasis.orthonormal.1 i
  have hsum : ∑ j, ((hA.isHermitian.eigenvectorBasis i).ofLp j) ^ 2
      = ‖hA.isHermitian.eigenvectorBasis i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact (Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]).symm
  have hdot : (hA.isHermitian.eigenvectorBasis i).ofLp ⬝ᵥ
      (hA.isHermitian.eigenvectorBasis i).ofLp
      = ∑ j, ((hA.isHermitian.eigenvectorBasis i).ofLp j) ^ 2 := by
    simp [dotProduct, sq]
  have hu : (hA.isHermitian.eigenvectorBasis i).ofLp ⬝ᵥ
      (hA.isHermitian.eigenvectorBasis i).ofLp = 1 := by
    rw [hdot, hsum, hnorm]
    norm_num
  exact eigen_le_of_unit hr hsub hu (hA.isHermitian.mulVec_eigenvectorBasis i)

/-- **The floor, in determinant form**: `r^(2n)·det A ≤ 1`.  The determinant is the product of the
eigenvalues, each of which is at most `r^{-2}` and nonnegative. -/
theorem det_mul_pow_le_one [DecidableEq (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {r : ℝ} (hr : 0 < r) (hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 → v ⬝ᵥ (A *ᵥ v) ≤ 1) :
    r ^ (2 * n) * A.det ≤ 1 := by
  have hHerm := hA.isHermitian
  have hprod : ∏ i, hHerm.eigenvalues i ≤ ∏ _i : Fin n, (r ^ 2)⁻¹ :=
    Finset.prod_le_prod (fun i _ => (hA.eigenvalues_pos i).le) (fun i _ => eigen_le hA hr hsub i)
  have hconst : (∏ _i : Fin n, (r ^ 2)⁻¹) = (r ^ (2 * n))⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, ← pow_mul]
  have hdet : A.det ≤ (r ^ (2 * n))⁻¹ := by
    rw [hHerm.det_eq_prod_eigenvalues]
    simpa using hprod.trans_eq hconst
  have hpos : (0:ℝ) < r ^ (2 * n) := by positivity
  have := mul_le_mul_of_nonneg_left hdet hpos.le
  rwa [mul_inv_cancel₀ (ne_of_gt hpos)] at this

/-! ## 4.  The floor in the engine's potential `volPot n A = (√det A)⁻¹` -/

/-- **`r^n ≤ volPot`.**  The engine's potential is `Φ = (det A)^{-1/2}`, so the determinant floor
`det A ≤ r^{-2n}` is exactly `Φ ≥ r^n`.  This is the number `brick-answer-producer` compares its
`ε` against. -/
theorem volPot_ge {Aq : Matrix (Fin n) (Fin n) ℚ}
    (hA : (QMCLeafB.EngineIterates.castM Aq).PosDef) {r : ℝ} (hr : 0 < r)
    (hsub : ∀ v : Fin n → ℝ,
      v ⬝ᵥ v ≤ r ^ 2 → v ⬝ᵥ (QMCLeafB.EngineIterates.castM Aq *ᵥ v) ≤ 1) :
    r ^ n ≤ QMCLeafB.EngineIterates.volPot n Aq := by
  classical
  have hdet := det_mul_pow_le_one hA hr hsub
  have hrn : (0:ℝ) < r ^ n := by positivity
  have hpos : (0:ℝ) < r ^ (2 * n) := by positivity
  have hr2n : r ^ (2 * n) = (r ^ n) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
  have hdetpos : (0:ℝ) < (QMCLeafB.EngineIterates.castM Aq).det := hA.det_pos
  have hdet' : (QMCLeafB.EngineIterates.castM Aq).det ≤ ((r ^ n)⁻¹) ^ 2 := by
    have h1 : (r ^ (2 * n))⁻¹ = ((r ^ n)⁻¹) ^ 2 := by
      rw [hr2n, inv_pow]
    rw [← h1]
    calc (QMCLeafB.EngineIterates.castM Aq).det
        = (r ^ (2 * n))⁻¹ * (r ^ (2 * n) * (QMCLeafB.EngineIterates.castM Aq).det) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      _ ≤ (r ^ (2 * n))⁻¹ * 1 := mul_le_mul_of_nonneg_left hdet (by positivity)
      _ = (r ^ (2 * n))⁻¹ := mul_one _
  have hsqrt : Real.sqrt ((QMCLeafB.EngineIterates.castM Aq).det) ≤ (r ^ n)⁻¹ := by
    calc Real.sqrt ((QMCLeafB.EngineIterates.castM Aq).det)
        ≤ Real.sqrt (((r ^ n)⁻¹) ^ 2) := Real.sqrt_le_sqrt hdet'
      _ = (r ^ n)⁻¹ := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hspos : (0:ℝ) < Real.sqrt ((QMCLeafB.EngineIterates.castM Aq).det) :=
    Real.sqrt_pos.2 hdetpos
  have hrninv : (0:ℝ) < (r ^ n)⁻¹ := by positivity
  calc r ^ n = ((r ^ n)⁻¹)⁻¹ := (inv_inv _).symm
    _ ≤ (Real.sqrt ((QMCLeafB.EngineIterates.castM Aq).det))⁻¹ :=
        (inv_le_inv₀ hrninv hspos).mpr hsqrt
    _ = QMCLeafB.EngineIterates.volPot n Aq := rfl

/-- **`r^n ≤ volPot` with the ball anywhere inside the ellipsoid**: the form the engine's terminal
containment actually supports. -/
theorem volPot_ge_of_ball_offset {Aq : Matrix (Fin n) (Fin n) ℚ}
    (hA : (QMCLeafB.EngineIterates.castM Aq).PosDef) {a b : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    (hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 →
      (b + v - a) ⬝ᵥ (QMCLeafB.EngineIterates.castM Aq *ᵥ (b + v - a)) ≤ 1) :
    r ^ n ≤ QMCLeafB.EngineIterates.volPot n Aq :=
  volPot_ge hA hr fun v hv => ray_le_of_ball_offset hA.posSemidef hsub hv

/-! ## 4′.  The floor as a closed *rational* comparison (the decidable stopping test)

The answer producer has to decide its branches with rational arithmetic.  `volPot` is a real square
root, which is the wrong thing to test; the floor is equivalent to the rational inequality
`det A ≤ (r^(2n))⁻¹`, and the loop's exit test `volPot ≤ ε` is `(ε²)⁻¹ ≤ det A`.  Composing the two
gives `ε ≥ r^n` — a closed rational contradiction with the chosen `ε < r^n`. -/

/-- **The floor in `ℚ`.**  For a rational radius `rq`, a rational positive definite shape matrix has
`det A ≤ (rq^(2n))⁻¹`.  This is decidable rational arithmetic. -/
theorem det_le_floor_rat {Aq : Matrix (Fin n) (Fin n) ℚ}
    (hA : (QMCLeafB.EngineIterates.castM Aq).PosDef) {rq : ℚ} (hrq : 0 < rq)
    (hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ (rq : ℝ) ^ 2 →
      v ⬝ᵥ (QMCLeafB.EngineIterates.castM Aq *ᵥ v) ≤ 1) :
    Aq.det ≤ (rq ^ (2 * n))⁻¹ := by
  have hr : (0:ℝ) < (rq : ℝ) := by exact_mod_cast hrq
  have h := det_mul_pow_le_one hA hr hsub
  have hdet : (QMCLeafB.EngineIterates.castM Aq).det = (Aq.det : ℝ) := by
    rw [QMCLeafB.EngineIterates.castM]
    exact (RingHom.map_det (Rat.castHom ℝ) Aq).symm
  have hq : rq ^ (2 * n) * Aq.det ≤ 1 := by
    have h3 : (rq : ℝ) ^ (2 * n) * (Aq.det : ℝ) ≤ 1 := by
      rw [← hdet]
      exact h
    exact_mod_cast h3
  have hpos : (0:ℚ) < rq ^ (2 * n) := by positivity
  calc Aq.det = (rq ^ (2 * n))⁻¹ * (rq ^ (2 * n) * Aq.det) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    _ ≤ (rq ^ (2 * n))⁻¹ * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (rq ^ (2 * n))⁻¹ := mul_one _

/-- **The rational floor with the ball anywhere inside the ellipsoid** — the form the answer
producer needs, since the margin ball sits at a fixed point while the iterate's centre moves. -/
theorem det_le_floor_rat_of_offset_ball {Aq : Matrix (Fin n) (Fin n) ℚ}
    (hA : (QMCLeafB.EngineIterates.castM Aq).PosDef) {a b : Fin n → ℝ} {rq : ℚ} (hrq : 0 < rq)
    (hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ (rq : ℝ) ^ 2 →
      (b + v - a) ⬝ᵥ (QMCLeafB.EngineIterates.castM Aq *ᵥ (b + v - a)) ≤ 1) :
    Aq.det ≤ (rq ^ (2 * n))⁻¹ :=
  det_le_floor_rat hA hrq fun v hv => ray_le_of_ball_offset hA.posSemidef hsub hv

/-- **The stopping test cannot fire.**  If the ball of radius `rq` is inside the body and the engine's
exit test `(ε²)⁻¹ ≤ det A` (equivalently `volPot ≤ ε`) fires, then `rq^n ≤ εq`.  So an answer
producer that picks `εq < rq^n` (e.g. `εq := rq^n / 2`) can never exit with the body still
nonempty. -/
theorem stop_test_forces {Aq : Matrix (Fin n) (Fin n) ℚ}
    (hA : (QMCLeafB.EngineIterates.castM Aq).PosDef) {rq εq : ℚ} (hrq : 0 < rq) (hεq : 0 < εq)
    (hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ (rq : ℝ) ^ 2 →
      v ⬝ᵥ (QMCLeafB.EngineIterates.castM Aq *ᵥ v) ≤ 1)
    (hstop : (εq ^ 2)⁻¹ ≤ Aq.det) :
    rq ^ n ≤ εq := by
  have hfloor := det_le_floor_rat hA hrq hsub
  have heps : (0:ℚ) < εq ^ 2 := pow_pos hεq 2
  have hrp : (0:ℚ) < rq ^ (2 * n) := pow_pos hrq _
  have h1 : rq ^ (2 * n) ≤ εq ^ 2 := (inv_le_inv₀ heps hrp).mp (hstop.trans hfloor)
  have hsq : rq ^ (2 * n) = (rq ^ n) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hsq] at h1
  have hrn : (0:ℚ) ≤ rq ^ n := (pow_pos hrq n).le
  nlinarith [h1, hrn, hεq.le, sq_nonneg (εq - rq ^ n), sq_nonneg (εq + rq ^ n)]

/-! ## 5.  The refutation: `Φ ≤ ε < r^n` empties the body -/

/-- **The numeric endgame of the loop.**  Let `body` be a feasible body that contains the Euclidean
ball of radius `r` around `a` and that is contained in the terminal ellipsoid `Ell A a`.  If the
terminal potential is at most `ε` and `ε < r^n`, then the body is empty.

This is the contradiction `r^n ≤ Φ_K ≤ ε < r^n` that the answer producer's *refuted-body* branch
runs on: the ball is supplied by `brick-ball-floor`, the containment and the potential by
`EngineIterates.engine_run`, and the comparison by this theorem. -/
theorem body_empty_of_floor {Aq : Matrix (Fin n) (Fin n) ℚ}
    (hA : (QMCLeafB.EngineIterates.castM Aq).PosDef) {a : Fin n → ℝ} {body : Set (Fin n → ℝ)}
    {r ε : ℝ} (hr : 0 < r)
    (hball : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 → a + v ∈ body)
    (hcov : ∀ z, z ∈ body → QMCLeafB.EngineIterates.Ell
      (QMCLeafB.EngineIterates.castM Aq) a z)
    (hvol : QMCLeafB.EngineIterates.volPot n Aq ≤ ε) (hε : ε < r ^ n) :
    ¬ ∃ z, z ∈ body := by
  have hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 →
      v ⬝ᵥ (QMCLeafB.EngineIterates.castM Aq *ᵥ v) ≤ 1 := by
    intro v hv
    have hmem : a + v ∈ body := hball v hv
    have hE : (a + v - a) ⬝ᵥ
        (QMCLeafB.EngineIterates.castM Aq *ᵥ (a + v - a)) ≤ 1 := hcov (a + v) hmem
    have hsub : a + v - a = v := by abel
    rwa [hsub] at hE
  have hfloor := volPot_ge hA hr hsub
  intro ⟨z, _hz⟩
  linarith

/-- **The refutation with the ball in `eucBallAt` form** (the shape `brick-ball-floor` states its
containment in). -/
theorem body_empty_of_eucBallAt {Aq : Matrix (Fin n) (Fin n) ℚ}
    (hA : (QMCLeafB.EngineIterates.castM Aq).PosDef) {a : Fin n → ℝ} {body : Set (Fin n → ℝ)}
    {r ε : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.EllipsoidVolume.eucBallAt a r ⊆ body)
    (hcov : ∀ z, z ∈ body → QMCLeafB.EngineIterates.Ell
      (QMCLeafB.EngineIterates.castM Aq) a z)
    (hvol : QMCLeafB.EngineIterates.volPot n Aq ≤ ε) (hε : ε < r ^ n) :
    ¬ ∃ z, z ∈ body := by
  refine body_empty_of_floor hA hr ?_ hcov hvol hε
  intro v hv
  exact hball ⟨v, hv, rfl⟩

/-- **The engine-shaped form.**  Instantiated at the `K`-th iterate of the GLS loop
(`Aq = Aat n A0 cd K`, `a = Cat n a0 cd K`): if the threshold body still contains the ball of radius
`r` at step `K`, then the run cannot have driven the potential below `r^n`. -/
theorem empty_of_terminal (A0 : Matrix (Fin n) (Fin n) ℚ)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData n) (a0 : Fin n → ℝ) (K : ℕ)
    {body : Set (Fin n → ℝ)} {r ε : ℝ}
    (hA : (QMCLeafB.EngineIterates.castM
      (QMCLeafB.EngineIterates.Aat n A0 cd K)).PosDef) (hr : 0 < r)
    (hball : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 →
      QMCLeafB.EngineIterates.Cat n a0 cd K + v ∈ body)
    (hcov : ∀ z, z ∈ body → QMCLeafB.EngineIterates.Ell
      (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat n A0 cd K))
      (QMCLeafB.EngineIterates.Cat n a0 cd K) z)
    (hvol : QMCLeafB.EngineIterates.volPot n
      (QMCLeafB.EngineIterates.Aat n A0 cd K) ≤ ε) (hε : ε < r ^ n) :
    ¬ ∃ z, z ∈ body :=
  body_empty_of_floor hA hr hball hcov hvol hε

/-- **The refutation in the geometry `engine_run` actually produces.**  The margin ball sits at
`b`, the terminal ellipsoid is centred at the running `a = Cat K`: the body is empty.  This is the
*refuted-body* branch in the exact shape the answer producer gets it. -/
theorem body_empty_of_ball_anywhere {Aq : Matrix (Fin n) (Fin n) ℚ}
    (hA : (QMCLeafB.EngineIterates.castM Aq).PosDef) {a b : Fin n → ℝ} {body : Set (Fin n → ℝ)}
    {r ε : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.EllipsoidVolume.eucBallAt b r ⊆ body)
    (hcov : ∀ z, z ∈ body → QMCLeafB.EngineIterates.Ell
      (QMCLeafB.EngineIterates.castM Aq) a z)
    (hvol : QMCLeafB.EngineIterates.volPot n Aq ≤ ε) (hε : ε < r ^ n) :
    ¬ ∃ z, z ∈ body := by
  have hsub : ∀ v : Fin n → ℝ, v ⬝ᵥ v ≤ r ^ 2 →
      (b + v - a) ⬝ᵥ (QMCLeafB.EngineIterates.castM Aq *ᵥ (b + v - a)) ≤ 1 := by
    intro v hv
    have hmem : b + v ∈ body := hball ⟨v, hv, rfl⟩
    exact hcov (b + v) hmem
  have hfloor := volPot_ge_of_ball_offset hA hr hsub
  intro ⟨z, _hz⟩
  linarith

/-! ## 6.  The capstone: `engine_run` plus a positive-margin ball refutes the body

`EngineIterates.engine_run` produces a run length `K` with `body ⊆ Ell (Aat K) (Cat K)` and
`volPot (Aat K) ≤ ε`.  Combined with the floor of §2′–§4 at that same `K`, a body that contains the
ball of radius `r` around a fixed point `b` — and that survives every recorded cut — cannot exist
once `ε < r^n`.  That is precisely the *refuted-body* verdict the answer producer has to return at
a threshold `t` whose body is empty: the ball is `brick-ball-floor`'s containment, the run and the
cuts are `brick-engine-iterates`/`brick-sep-oracle`, and the numerical contradiction is here. -/
theorem engine_run_refutes {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → QMCLeafB.EngineIterates.CutData n}
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef)
    (hwit : ∀ k, QMCLeafB.EngineIterates.Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (a0 : Fin n → ℝ) (body : (Fin n → ℝ) → Prop)
    (hcover : ∀ z, body z →
      QMCLeafB.EngineIterates.Ell (QMCLeafB.EngineIterates.castM A0) a0 z)
    (hcut : ∀ k z, body z →
      -(((cd k).rho : ℝ) * QMCLeafB.EngineIterates.sqrtSigmaR
          (QMCLeafB.EngineIterates.cutCR cd k) (QMCLeafB.EngineIterates.cutPR cd k))
        ≤ QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
          (z - QMCLeafB.EngineIterates.Cat n a0 cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    (hcontract : 1 < QMCLeafB.EngineIterates.rho0R n (ρmax : ℝ))
    {ε : ℝ} (hεpos : 0 < ε) {b : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.EllipsoidVolume.eucBallAt b r ⊆ body)
    (hε : ε < r ^ n) :
    ¬ ∃ z, body z := by
  obtain ⟨K, hcov, hvol⟩ :=
    QMCLeafB.EngineIterates.engine_run hn hA0 hwit hρ hcne a0 body hcover hcut
      hρmax hle hcontract hεpos
  exact body_empty_of_ball_anywhere
    (QMCLeafB.EngineIterates.Aat_cast_posDef hn hA0 hwit hρ hcne K) hr hball hcov hvol hε

/-! ## 7.  The constant ledger (closed arithmetic of the campaign) -/

/-- The bisection width after thirteen calls is `2^13 = 8192`, and the objective gap is the quarter
of it: `V/32768`. -/
theorem thirteen_calls : (2:ℚ) ^ 13 = 8192 ∧ (4:ℚ) * 2 ^ 13 = 32768 :=
  ⟨by norm_num, by norm_num⟩

/-- `V/32768 ≤ V/20000` for `V ≥ 0`: the thirteen-call bracket already meets the leaf's slack. -/
theorem gap_le_slack {V : ℝ} (hV : 0 ≤ V) : V / (4 * 2 ^ 13) ≤ V / 20000 := by
  have h1 : ((4:ℝ) * 2 ^ 13) = 32768 := by norm_num
  rw [h1]
  exact div_le_div_of_nonneg_left hV (by norm_num) (by norm_num)

/-- `V = 2W` turns the driver's `V/20000` slack into the leaf's `W/10000`. -/
theorem v_split {W : ℝ} : (2 * W) / 20000 = W / 10000 := by
  have h : (20000:ℝ) = 2 * 10000 := by norm_num
  rw [h, mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]

/-- Halving a positive target keeps it positive and strictly smaller: the `ε` of the stopping rule. -/
theorem eps_half {x : ℝ} (hx : 0 < x) : 0 < x / 2 ∧ x / 2 < x := by
  constructor <;> linarith

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.NumericEndgame.dot_self_nonneg
#print axioms QMCLeafB.NumericEndgame.dot_self_pos
#print axioms QMCLeafB.NumericEndgame.smul_dot_self
#print axioms QMCLeafB.NumericEndgame.smul_qf
#print axioms QMCLeafB.NumericEndgame.qf_add_expand
#print axioms QMCLeafB.NumericEndgame.thirteen_calls
#print axioms QMCLeafB.NumericEndgame.eps_half
#print axioms QMCLeafB.NumericEndgame.ray_le_of_ball
#print axioms QMCLeafB.NumericEndgame.eigen_le_of_unit
#print axioms QMCLeafB.NumericEndgame.eigen_le
#print axioms QMCLeafB.NumericEndgame.det_mul_pow_le_one
#print axioms QMCLeafB.NumericEndgame.ray_le_of_ball_offset
#print axioms QMCLeafB.NumericEndgame.volPot_ge
#print axioms QMCLeafB.NumericEndgame.volPot_ge_of_ball_offset
#print axioms QMCLeafB.NumericEndgame.body_empty_of_ball_anywhere
#print axioms QMCLeafB.NumericEndgame.det_le_floor_rat
#print axioms QMCLeafB.NumericEndgame.det_le_floor_rat_of_offset_ball
#print axioms QMCLeafB.NumericEndgame.stop_test_forces
#print axioms QMCLeafB.NumericEndgame.body_empty_of_floor
#print axioms QMCLeafB.NumericEndgame.body_empty_of_eucBallAt
#print axioms QMCLeafB.NumericEndgame.empty_of_terminal
#print axioms QMCLeafB.NumericEndgame.engine_run_refutes
#print axioms QMCLeafB.NumericEndgame.gap_le_slack
#print axioms QMCLeafB.NumericEndgame.v_split

end QMCLeafB.NumericEndgame


