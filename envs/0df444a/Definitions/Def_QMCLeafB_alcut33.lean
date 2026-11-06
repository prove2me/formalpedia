-- Prove2me | Definitions.Def_QMCLeafB_alcut33
-- name    : QMCLeafB_alcut33
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:44:02.448614+00:00
-- url     : https://prove2.me/theorems/b1dbb992-677f-4ec8-9f0e-b19e71761336
-- title:
--   QMCLeafB alcut33
-- statement:
--   # `Check_alcut33_m2` — phase 33, member m2, direction `allcut-records` (d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_m2
/-
# `Check_alcut33_m2` — phase 33, member m2, direction `allcut-records` (d2)

## The question (charter, direction 2)

Direction (B): at a point where **no** round reports `ok`, build `RunParts o G t (P G)` with
`ok ≡ false`, i.e. serve `RunParts.hcut` for every round below the horizon.  The banked class
builder is `CruxM1.allFalseParts` (seven engine slots + the separation slot).  The charter asks the
falsify-first question: **is `hcut` satisfiable at all under the campaign's `rmax`-bounded
margin `del ≤ ρ·√σ`?**

## The answer proved here: no, unless the body carries no cube of side `dq/(4(c_A+1))`

`RunParts.hcut` is a *transcript* condition, but the transcript also drives the ellipsoid: the
banked containment invariant (`SimLoop.Prefix.body_containment_at_halving_margin_prefix`) puts the
whole run body inside the terminal ellipsoid `Ell A_T a_T`, and the banked halving
budget (`RunParams.hbudget`) makes `volPot A_T < r ^ (n·n)` with `r = dq/(8(c_A+1))`.  Hence **any**
all-`false` run forces the run body to fit in an ellipsoid whose determinant potential is below
`r ^ (n·n)`.

The banked `BallM2.no_runParts_of_ball` exploits this with a *ball* in the body.  This file
generalises it to an arbitrary **axis-aligned cube** of side `ℓ`:

* `qfR_le_four_of_cube` — a cube in `Ell A a` forces `xᵀAx ≤ 4` on the doubled cube (the
  two-antipodal-points / parallelogram argument, no symmetry of `A` needed beyond `PosSemidef`);
* `qfR_le_of_cube` — the scaling argument upgrades this to the Loewner bound
  `xᵀAx ≤ (4/ℓ²)·‖x‖²`, i.e. `(ℓ²/4)·A ⪯ 1`;
* `det_le_of_cube` — the banked spectral determinant ceiling `BallFloor.det_le_one_of_qf_le`
  turns that into `det A ≤ (4/ℓ²)^(n·n)`, i.e. `volPot A ≥ (ℓ/2)^(n·n)`;
* `bit_true_of_cube` — so if the run body contains a cube of side `ℓ > 2r` then **every**
  `RunParts` at the point forces the bit `true`.

That is a strict generalisation of the ball obstruction (a ball of radius `R` carries a cube of side
`2R/√d`, so the cube test is weaker by `√d` — but for bodies that are *thin in one direction and fat
in the others*, which is exactly the thin band, the cube test fires where the ball test cannot).

## Consequence for direction (B) — the named residual

`allFalse_needs_no_cube`: an all-`false` record at `(G,t)` forces the run body to contain **no**
axis-aligned cube of side `2r = dq/(4(c_A+1))`.  So the all-cut record class lives only on
*box-free* bodies — at the campaign's constants a `Θ(dq²)`-thin stratum at each input.  Everywhere
else the record must report `ok`, i.e. the leftover of the `Sound31` interface is **not** closable by
all-false records and the leaf's content is the witness side (`m3`'s (A) rounding, banked by `m4`).

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom audit at the end (expected `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Alcut33M2

open QuantumMaxCutEnergy
open QMCLeafB.BallFloor

/-! ## 1.  The cube and the two-point bound -/

/-- The axis-aligned closed cube of side `ℓ` around `c`, in the flat coordinates. -/
def cube {N : ℕ} (c : Fin N → ℝ) (ℓ : ℝ) : Set (Fin N → ℝ) :=
  {z | ∀ i, |z i - c i| ≤ ℓ / 2}

theorem mem_cube {N : ℕ} {c z : Fin N → ℝ} {ℓ : ℝ} :
    z ∈ cube c ℓ ↔ ∀ i, |z i - c i| ≤ ℓ / 2 := Iff.rfl

/-- **Two antipodal points of the cube.**  `qfR A v ≤ 1` at both `c ± v/2` forces `qfR A v ≤ 4`: the
parallelogram identity `qfR u₊ + qfR u₋ = 2 qfR ((u₊-u₋)/2) + 2 qfR ((u₊+u₋)/2)` plus positivity of
the second term (this is `PosSemidef`, and no symmetry of `A` is used beyond it). -/
theorem qfR_le_four_of_cube {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hpsd : A.PosSemidef)
    {a c : Fin N → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hbox : cube c ℓ ⊆ Ell A a)
    {v : Fin N → ℝ} (hv : ∀ i, |v i| ≤ ℓ) :
    qfR A v ≤ 4 := by
  have hmem : ∀ t : ℝ, |t| ≤ 1 / 2 → c + t • v ∈ cube c ℓ := by
    intro t ht i
    have h1 : (c + t • v) i - c i = t * v i := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1, abs_mul]
    calc |t| * |v i| ≤ (1 / 2) * ℓ := by
          refine mul_le_mul ht (hv i) (abs_nonneg _) (by norm_num)
      _ = ℓ / 2 := by ring
  have e1 : c + (1 / 2 : ℝ) • v - a = (1 / 2 : ℝ) • v + (c - a) := by abel
  have e2 : c + (-(1 / 2) : ℝ) • v - a = -((1 / 2 : ℝ) • v) + (c - a) := by
    rw [neg_smul]
    abel
  have hplus : qfR A ((1 / 2 : ℝ) • v + (c - a)) ≤ 1 := by
    have h := hbox (hmem (1 / 2) (by norm_num))
    have h' : (c + (1 / 2 : ℝ) • v - a) ⬝ᵥ (A *ᵥ (c + (1 / 2 : ℝ) • v - a)) ≤ 1 := by
      simpa only [Ell, Set.mem_ofPred_eq] using h
    rw [e1] at h'
    simpa only [qfR] using h'
  have hminus : qfR A (-((1 / 2 : ℝ) • v) + (c - a)) ≤ 1 := by
    have h := hbox (hmem (-(1 / 2 : ℝ)) (by norm_num))
    have h' : (c + (-(1 / 2) : ℝ) • v - a) ⬝ᵥ (A *ᵥ (c + (-(1 / 2) : ℝ) • v - a)) ≤ 1 := by
      simpa only [Ell, Set.mem_ofPred_eq] using h
    rw [e2] at h'
    simpa only [qfR] using h'
  have hpar := qfR_add_vec_add_neg A ((1 / 2 : ℝ) • v) (c - a)
  have hnonneg : 0 ≤ qfR A (c - a) := by
    have h := hpsd.dotProduct_mulVec_nonneg (c - a)
    simpa [qfR, star_trivial] using h
  have hhalf : qfR A ((1 / 2 : ℝ) • v) ≤ 1 := by linarith
  have hsq : qfR A ((1 / 2 : ℝ) • v) = (1 / 4) * qfR A v := by
    rw [qfR_smul_vec]; norm_num
  rw [hsq] at hhalf
  linarith

/-! ## 2.  Scaling: the cube forces a Loewner bound -/

/-- **The cube gives `(ℓ²/4)·A ⪯ 1`.**  Scaling any `x` into the doubled cube by `t = ℓ/‖x‖`:
`|t x i| ≤ ‖x‖ · t = ℓ`, so `qfR A (t x) ≤ 4` and hence `t² · qfR A x ≤ 4`. -/
theorem qfR_le_of_cube {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hpsd : A.PosSemidef)
    {a c : Fin N → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hbox : cube c ℓ ⊆ Ell A a) (x : Fin N → ℝ) :
    (ℓ ^ 2 / 4) * qfR A x ≤ ∑ i, x i ^ 2 := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp [qfR]
  have hS : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      exact hx (funext (by simpa [not_exists] using h))
    refine Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ i, ?_⟩
    rw [sq]
    exact mul_self_pos.mpr hi
  set R : ℝ := Real.sqrt (∑ i, x i ^ 2) with hR
  have hRpos : 0 < R := Real.sqrt_pos.2 hS
  have hRsq : R ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hS.le
  have hcoord : ∀ i, |x i| ≤ R := by
    intro i
    have h1 : (x i) ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
        (Finset.mem_univ i)
    calc |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ j, x j ^ 2) := Real.sqrt_le_sqrt h1
      _ = R := rfl
  set t : ℝ := ℓ / R with ht
  have hv : ∀ i, |(t • x) i| ≤ ℓ := by
    intro i
    have h1 : (t • x) i = t * x i := by simp
    rw [h1, abs_mul, ht, abs_of_pos (div_pos hℓ hRpos)]
    have h2 : 0 ≤ ℓ / R := (div_pos hℓ hRpos).le
    calc ℓ / R * |x i| ≤ ℓ / R * R := mul_le_mul_of_nonneg_left (hcoord i) h2
      _ = ℓ := by field_simp
  have h4 := qfR_le_four_of_cube hpsd hℓ hbox hv
  have hscale : qfR A (t • x) = t ^ 2 * qfR A x := qfR_smul_vec t A x
  rw [hscale] at h4
  have ht2 : t ^ 2 = ℓ ^ 2 / (∑ i, x i ^ 2) := by
    rw [ht, div_pow, hRsq]
  rw [ht2, div_mul_eq_mul_div, div_le_iff₀ hS] at h4
  linarith

/-! ## 3.  The determinant ceiling -/

/-- **A cube in the ellipsoid floors the volume potential.**  `det A ≤ (4/ℓ²)^N`, i.e.
`(ℓ/2)^N ≤ volPot A`.  Route: `(ℓ²/4)·A ⪯ 1` (`qfR_le_of_cube`) into the banked spectral ceiling
`BallFloor.det_le_one_of_qf_le`, then `det (λ•A) = λ^N det A`. -/
theorem det_le_of_cube {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hpsd : A.PosSemidef)
    {a c : Fin N → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hbox : cube c ℓ ⊆ Ell A a) :
    A.det ≤ (4 / ℓ ^ 2) ^ N := by
  have hscal : (0 : ℝ) ≤ ℓ ^ 2 / 4 := by positivity
  have hpsdscal : ((ℓ ^ 2 / 4) • A).PosSemidef := hpsd.smul hscal
  have hone : ((ℓ ^ 2 / 4) • A).det ≤ 1 := by
    refine det_le_one_of_qf_le hpsdscal (fun x => ?_)
    rw [qfR_smul]
    exact qfR_le_of_cube hpsd hℓ hbox x
  rw [Matrix.det_smul, Fintype.card_fin] at hone
  have hpow : (0 : ℝ) < (ℓ ^ 2 / 4) ^ N := by positivity
  have h2 : A.det ≤ 1 / (ℓ ^ 2 / 4) ^ N :=
    (le_div_iff₀ hpow).mpr (by rw [mul_comm]; exact hone)
  have h3 : 1 / (ℓ ^ 2 / 4) ^ N = (4 / ℓ ^ 2) ^ N := by
    rw [← one_pow N, ← div_pow]
    congr 1
    field_simp
  rw [h3] at h2
  exact h2

/-- The same ceiling in `volPot` form: `(ℓ/2)^N ≤ volPot N A`. -/
theorem pow_le_volPot_of_cube {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ} (hA : (castM A).PosDef)
    {a c : Fin N → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hbox : cube c ℓ ⊆ Ell (castM A) a) :
    (ℓ / 2) ^ N ≤ volPot A := by
  have hdet := det_le_of_cube hA.posSemidef hℓ hbox
  have hdetpos : 0 < (castM A).det := hA.det_pos
  have hsqrt : Real.sqrt ((castM A).det) ≤ (2 / ℓ) ^ N := by
    have h1 : Real.sqrt ((castM A).det) ≤ Real.sqrt ((4 / ℓ ^ 2) ^ N) := Real.sqrt_le_sqrt hdet
    have h2 : Real.sqrt ((4 / ℓ ^ 2) ^ N) = (2 / ℓ) ^ N := by
      have hbase : (4 / ℓ ^ 2) = (2 / ℓ) ^ 2 := by field_simp; ring
      rw [hbase, ← pow_mul, mul_comm 2 N, pow_mul, Real.sqrt_sq (by positivity)]
    rwa [h2] at h1
  have hspos : 0 < Real.sqrt ((castM A).det) := Real.sqrt_pos.2 hdetpos
  have h2pos : 0 < (2 / ℓ) ^ N := by positivity
  have hfin : ((2 / ℓ) ^ N)⁻¹ ≤ (Real.sqrt ((castM A).det))⁻¹ :=
    inv_le_inv₀ h2pos hspos |>.mpr hsqrt
  have hrw : ((2 / ℓ) ^ N)⁻¹ = (ℓ / 2) ^ N := by
    have hbase : (2 / ℓ) = (ℓ / 2)⁻¹ := by field_simp
    rw [hbase, inv_pow, inv_inv]
  rw [hrw] at hfin
  exact hfin

/-! ## 4.  The all-cut obstruction: a cube in the body forces the bit `true`

`RunParts` at a `false` bit makes *every* round below the horizon a cut round, so the banked
containment invariant puts the whole run body inside the terminal ellipsoid `Ell A_T a_T` while the
banked halving budget gives `volPot A_T < r ^ (n·n)`.  A cube of side `ℓ > 2r` in the body is then
inside `Ell A_T a_T`, so `volPot A_T ≥ (ℓ/2)^(n·n) > r ^ (n·n)` — a contradiction.
-/

/-- **A cube of side `ℓ > 2r` in the run body forces the bit `true`.**  `r = dq/(8(c_A+1))` is the
campaign ball radius (`RunParams.hbudget`'s constant).  This is the cube analogue of
`BallM2.no_runParts_of_ball`, and it is strictly more general: every ball of radius `R` contains a
cube of side `2R/√d`, but a *thin-slab* body (thin in one direction, fat in the others) can carry a
cube of side far above `2r` while carrying no ball of radius `r`. -/
theorem bit_true_of_cube {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {c : Fin (G.n * G.n) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcube : cube c ℓ ⊆ QMCLeafB.BallM2.runBall G t P)
    (hbig : 2 * (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) < ℓ)
    (B : QMCLeafB.FinalStroke.RunParts o G t P) :
    o G t = true := by
  classical
  by_contra hcon
  have hfalse : o G t = false := by
    cases h : o G t with
    | false => rfl
    | true => exact absurd h hcon
  have hall : ∀ k, k < P.K * P.m → B.ok k = false :=
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).mp
      (by rw [← B.hverdict]; exact hfalse)
  have hNm : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by nlinarith [P.hdq]
  have hn' : 2 ≤ G.n * G.n := by nlinarith
  have hA0 : (QMCLeafB.EngineIterates.castM
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).PosDef :=
    QMCLeafB.Boundary.initShapeOf_cast_posDef hNm
  have hwit : ∀ k, k < P.K * P.m →
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd k *ᵥ (B.cd k).p = (B.cd k).c :=
    fun k hk => B.hwit k hk (hall k hk)
  have hρ : ∀ k, k < P.K * P.m → 0 ≤ (B.cd k).rho :=
    fun k hk => B.hrho k hk (hall k hk)
  have hcne : ∀ k, k < P.K * P.m → (B.cd k).c ≠ 0 :=
    fun k hk => B.hcne k hk (hall k hk)
  have hcover : ∀ z, QMCLeafB.BallM2.runBall G t P z →
      QMCLeafB.EngineIterates.Ell (QMCLeafB.EngineIterates.castM
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))) 0 z :=
    fun z hz => QMCLeafB.Boundary.ell_initShapeOf hNm (QMCLeafB.Boundary.relaxBall_norm hz)
  have hδ0 : ∀ k, k < P.K * P.m → 0 ≤ B.del k :=
    fun k hk => B.hdel0 k hk (hall k hk)
  have hcheck : ∀ k, k < P.K * P.m →
      (B.del k) ^ 2 ≤ ((B.cd k).rho) ^ 2 *
        QMCLeafB.EngineIterates.sigmaQ (B.cd k).c (B.cd k).p :=
    fun k hk => B.hcheck k hk (hall k hk)
  have hcutδ : ∀ k, k < P.K * P.m → ∀ z, QMCLeafB.BallM2.runBall G t P z →
      -(((B.del k : ℚ)) : ℝ) ≤ QMCLeafB.EngineIterates.cutCR B.cd k
        ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k) :=
    fun k hk z hz => B.hcut k hk (hall k hk) z hz
  have hle : ∀ k, k < P.K * P.m → (B.cd k).rho ≤ P.rmax :=
    fun k hk => B.hle k hk (hall k hk)
  obtain ⟨hcont, hvol⟩ := QMCLeafB.SimLoop.Prefix.body_containment_at_halving_margin_prefix
    (n := G.n * G.n) hn' (A0 := QMCLeafB.Boundary.initShapeOf (G.n * G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) (cd := B.cd) (T := P.K * P.m)
    hA0 hwit hρ hcne (0 : Fin (G.n * G.n) → ℝ) (QMCLeafB.BallM2.runBall G t P) hcover hδ0 hcheck
    hcutδ P.hrmax hle P.hhalve
    (le_rfl : QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K ≤
      QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K) le_rfl
  have hKpd : (QMCLeafB.BallFloor.castM (QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))).PosDef :=
    QMCLeafB.SimLoop.Aat_cast_posDef_prefix hn' hA0 hwit hρ hcne (P.K * P.m) le_rfl
  -- the cube sits in the terminal ellipsoid
  have hcubeEll : cube c ℓ ⊆ QMCLeafB.BallFloor.Ell (QMCLeafB.BallFloor.castM
      (QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m)))
      (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd (P.K * P.m)) :=
    fun z hz => hcont z (hcube hz)
  have hfloor : (ℓ / 2) ^ (G.n * G.n) ≤
      QMCLeafB.BallFloor.volPot (QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m)) :=
    pow_le_volPot_of_cube hKpd hℓ hcubeEll
  -- the halving budget
  have hr : (0 : ℝ) < ((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1)) := by
    have h1 : (0 : ℝ) < (P.dq : ℝ) := by exact_mod_cast P.hdq
    have h2 : (0 : ℝ) ≤ (P.cAq : ℝ) := by exact_mod_cast P.hcAq
    positivity
  have hpot : QMCLeafB.BallFloor.volPot (QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))
      < (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) ^ (G.n * G.n) :=
    lt_of_le_of_lt hvol P.hbudget
  have hlt : (ℓ / 2) ^ (G.n * G.n)
      < (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) ^ (G.n * G.n) :=
    lt_of_le_of_lt hfloor hpot
  have hroot : ℓ / 2 < ((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1)) :=
    lt_of_pow_lt_pow_left₀ (G.n * G.n) hr.le hlt
  linarith

#print axioms QMCLeafB.Alcut33M2.bit_true_of_cube

/-- **The named residual of the all-cut class.**  An all-`false` run at `(G,t)` forces the run body
to contain **no** axis-aligned cube of side above `2r = dq/(4(c_A+1))`.  So "all-cut record" is
confined to *cube-free* bodies: at the campaign's constants that is a `Θ(dq²)`-thin stratum, and in
particular the thin band of the charter (thickness `Θ(dq)`) is **not** in it. -/
theorem no_cube_of_allFalse {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} (hbit : o G t = false)
    {c : Fin (G.n * G.n) → ℝ} {ℓ : ℝ}
    (hcube : cube c ℓ ⊆ QMCLeafB.BallM2.runBall G t P)
    (B : QMCLeafB.FinalStroke.RunParts o G t P) :
    ℓ ≤ 2 * (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) := by
  by_contra hcon
  have hbig : 2 * (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) < ℓ := not_le.mp hcon
  have hr : (0 : ℝ) < ((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1)) := by
    have h1 : (0 : ℝ) < (P.dq : ℝ) := by exact_mod_cast P.hdq
    have h2 : (0 : ℝ) ≤ (P.cAq : ℝ) := by exact_mod_cast P.hcAq
    positivity
  have hℓ : 0 < ℓ := by linarith
  have htrue := bit_true_of_cube hn hℓ hcube hbig B
  rw [hbit] at htrue
  exact Bool.noConfusion htrue

#print axioms QMCLeafB.Alcut33M2.no_cube_of_allFalse

end QMCLeafB.Alcut33M2


