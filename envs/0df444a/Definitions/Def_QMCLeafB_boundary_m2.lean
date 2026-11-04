-- Prove2me | Definitions.Def_QMCLeafB_boundary_m2
-- name    : QMCLeafB_boundary_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:06:44.517056+00:00
-- url     : https://prove2.me/theorems/8d9d8884-57f0-4d2c-b6a6-72ca2b5924ae
-- title:
--   QMCLeafB boundary_m2
-- statement:
--   # leaf B phase 7 — brick `boundary` (swarm `smvzzjm07`, member m2, direction d8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_EngineIterates
import Definitions.Def_QMCLeafB_NumericEndgame_m3
import Definitions.Def_QMCLeafB_answer_producer
import Definitions.Def_QMCLeafB_ball_floor
/-
# leaf B phase 7 — brick `boundary` (swarm `smvzzjm07`, member m2, direction d8)

The simulation's two *boundary* objects, which no other brick owns.

**(A) Init.**  The ellipsoid loop has always been stated with a free starting shape `A0`, a free
centre `a0`, and two hypotheses nobody discharged: `hA0 : (castM A0).PosDef` and
`hcover : ∀ z, body z → Ell (castM A0) a0 z`.  Here both are *constructed*:

* `initShapeOf N M = M⁻¹ • 1` is the ellipsoid of radius `√M` around `0`; `ell_initShapeOf` proves
  it covers every point of norm-squared at most `M`, and `initShapeOf_cast_posDef` proves `hA0`.
  `volPot_initShapeOf` gives the **closed form** `Φ₀ = (√M)^N` of the starting potential, the
  number the height/length ledger and the round count both need (`log Φ₀ = (N/2)·log M`).
* `initShape N = N⁻¹ • 1` is the choice for the campaign's own body
  `AnswerProducer.StrictBody A t εr` (flattened unit-diagonal semidefinite matrices with
  `tr (A Z) ≤ t − εr`): every entry of such a matrix lies in `[-1,1]`, so
  `‖flat Z‖² = ∑ᵢⱼ Zᵢⱼ² ≤ n²` (`sum_sq_flat`, `sum_sq_le_of_strictBody`) and
  `initEll_covers_strictBody` discharges `hcover`, `volPot_initShape` gives `Φ₀ = (√N)^N`.

**(B) Extract.**  The engine theorems delivered so far (`EngineIterates.engine_run`,
`engine_run_margin`) are *existential* in the run length: they say `∃ K, …`.  A `Poly` program has
no fuel it can guess — it must run a **fixed, closed-form** number of rounds.  This file supplies
the halving-shaped (no logarithms, no square roots of rationals to evaluate) run theorem at the
*explicit* round count `T₀ = K · m`:

* `body_containment_at_halving` — both conclusions of `engine_run` at round `T₀`;
* `body_containment_at_halving_margin` — the same from the separation oracle's *absolute* margins
  `δ k` (the interface `brick-sep-oracle` actually reports: `δ² ≤ ρ²σ` as an exact rational test);
* `strictBody_refuted_at_halving` — the capstone: with `A0 = initShapeOf` and `a0 = 0` wired in, a
  run of exactly `T₀` rounds whose cuts all leave the ball-carrying relaxation `W` inside the
  halfspaces refutes the threshold with its slack.  The conclusion is *verbatim* the `false`
  clause of `FinishLine.SoundεOnBracket`;
* `strictBody_refuted` — the same with the ball floor of `Check_ball_floor` plugged in
  (`relaxBall_of_ballFloor`): no ball hypotheses left, only the radius `δ/(8(c_A+1))` and
  `cA ≥ ∑ᵢⱼ|Aᵢⱼ|`;
* `relaxBall`, `strictBody_ball_relaxBall`, `strictBody_refuted_final`,
  `exists_M`, `strictBody_refuted_concrete` — the last quantitative hypothesis closed: the
  relaxation is given the norm bound `M` explicitly (`M = 2n² + 2δ²` works), so
  `strictBody_refuted_concrete` needs no radius side condition at all.

The deliverable has 25 audited declarations, all on the standard three axioms.

**A design correction this file also records** (see `strictBody_refuted_at_halving`'s docstring):
`AnswerProducer.squeeze_of_engine` derives its determinant floor from
`hball : ∀ u, StrictBody u → eucBall u r ⊆ StrictBody`, which is **false** — a Euclidean ball
around a unit-diagonal `Z` leaves the affine slice `Zᵢᵢ = 1` immediately.  The floor must be routed
through a ball-carrying *relaxation* `W ⊇ StrictBody` (exactly what
`BallFloor.ball_subset_relaxBodyLE` produces), so the engine has to run on `W`, not on
`StrictBody`.  Every theorem below keeps `W` as a parameter for that reason.

No `sorry`, no `axiom`; imports are `Mathlib` plus the compiled campaign library.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.Boundary

open QMCLeafB.EngineIterates

/-! ## 1.  The initial ellipsoid `A₀ = M⁻¹ • 1` -/

/-- **The starting shape matrix of the loop in dimension `N`, at radius `√M`**: `M⁻¹ • 1`.  Every
point of norm-squared at most `M` lies in its ellipsoid, so `M` is exactly the "how big is the
body" number the init step has to supply.  `M⁻¹` (not `M⁻²`) is what the ledger wants:
`Φ₀ = (√M)^N`. -/
noncomputable def initShapeOf (N : ℕ) (M : ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  M⁻¹ • (1 : Matrix (Fin N) (Fin N) ℚ)

/-- The real cast of the starting shape: `(M : ℝ)⁻¹ • 1`. -/
theorem castM_initShapeOf (N : ℕ) (M : ℚ) :
    castM (initShapeOf N M) = ((M : ℝ)⁻¹) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  by_cases h : i = j <;> simp [initShapeOf, castM, Matrix.smul_apply, h]

/-- **The starting shape is positive definite** — the `hA0` hypothesis of every engine theorem. -/
theorem initShapeOf_cast_posDef {N : ℕ} {M : ℚ} (hM : 0 < M) :
    (castM (initShapeOf N M)).PosDef := by
  rw [castM_initShapeOf]
  have hpos : (0 : ℝ) < (M : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hM)
  exact (Matrix.PosDef.one (n := Fin N) (R := ℝ)).smul hpos

/-- **The starting ellipsoid covers every point of norm-squared at most `M`.** -/
theorem ell_initShapeOf {N : ℕ} {M : ℚ} (hM : 0 < M) {z : Fin N → ℝ}
    (hz : ∑ i, z i ^ 2 ≤ (M : ℝ)) :
    Ell (castM (initShapeOf N M)) (0 : Fin N → ℝ) z := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hmv : (((M : ℝ)⁻¹) • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ z = ((M : ℝ)⁻¹) • z := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdot : z ⬝ᵥ z = ∑ i, z i ^ 2 := by
    simp [dotProduct, sq]
  show (z - 0) ⬝ᵥ (castM (initShapeOf N M) *ᵥ (z - 0)) ≤ 1
  rw [sub_zero, castM_initShapeOf, hmv, dotProduct_smul, smul_eq_mul, hdot]
  calc (M : ℝ)⁻¹ * ∑ i, z i ^ 2 ≤ (M : ℝ)⁻¹ * (M : ℝ) :=
        mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (le_of_lt (by exact_mod_cast hM)))
    _ = 1 := by rw [inv_mul_cancel₀ hMne]

/-- **The starting potential in closed form**: `Φ₀ = (√M)^N`, i.e. `log Φ₀ = (N/2)·log M`.  This
is the number the round count `K` has to clear. -/
theorem volPot_initShapeOf (N : ℕ) {M : ℚ} (hM : 0 < M) :
    volPot N (initShapeOf N M) = (Real.sqrt (M : ℝ)) ^ N := by
  have hx : (0 : ℝ) ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt (by exact_mod_cast hM))
  have hsp : ∀ k : ℕ, Real.sqrt (((M : ℝ)⁻¹) ^ k) = Real.sqrt ((M : ℝ)⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k) ((M : ℝ)⁻¹), ih, pow_succ]
  rw [volPot, castM_initShapeOf, Matrix.det_smul, Matrix.det_one, mul_one, hsp, Real.sqrt_inv,
    inv_pow, inv_inv, Fintype.card_fin]

/-! ### 1.1  The choice for the campaign's own body: `M = N` -/

/-- **The starting shape for the strict threshold body**: `N⁻¹ • 1`, radius `√N`. -/
noncomputable def initShape (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  initShapeOf N (N : ℚ)

theorem castM_initShape (N : ℕ) :
    castM (initShape N) = ((N : ℝ)⁻¹) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  rw [initShape, castM_initShapeOf]
  push_cast
  rfl

/-- The `hA0` slot of every engine theorem, discharged at `A₀ = initShape N`. -/
theorem initShape_cast_posDef {N : ℕ} (hN : 0 < N) : (castM (initShape N)).PosDef :=
  initShapeOf_cast_posDef (N := N) (by exact_mod_cast hN)

/-- The `hcover` slot at round `0`, for the campaign's strict threshold body. -/
theorem ell_initShape {N : ℕ} (hN : 0 < N) {z : Fin N → ℝ}
    (hz : ∑ i, z i ^ 2 ≤ (N : ℝ)) :
    Ell (castM (initShape N)) (0 : Fin N → ℝ) z := by
  rw [initShape]
  exact ell_initShapeOf (by exact_mod_cast hN) hz

/-- **`flat` preserves the sum of squares**: `‖flat X‖² = ∑ᵢⱼ Xᵢⱼ²`. -/
theorem sum_sq_flat {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    ∑ k : Fin (n * n), (QMCLeafB.AnswerProducer.flat X) k ^ 2 = ∑ i, ∑ j, X i j ^ 2 := by
  rw [← Equiv.sum_comp finProdFinEquiv (fun k => (QMCLeafB.AnswerProducer.flat X) k ^ 2)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [QMCLeafB.AnswerProducer.flat]

/-- **Every point of the flattened threshold body has norm-squared at most `n²`.** -/
theorem sum_sq_le_of_strictBody {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {t εr : ℚ}
    {z : Fin (n * n) → ℝ} (hz : QMCLeafB.AnswerProducer.StrictBody A t εr z) :
    ∑ k, z k ^ 2 ≤ (n * n : ℝ) := by
  obtain ⟨Z, hZ, -, rfl⟩ := hz
  rw [sum_sq_flat]
  have hterm : ∀ i j : Fin n, Z i j ^ 2 ≤ 1 := by
    intro i j
    have h1 : |Z i j| ≤ 1 := QMCLeafB.AnswerProducer.abs_apply_le_one hZ i j
    have h2 : Z i j ^ 2 = |Z i j| ^ 2 := (sq_abs (Z i j)).symm
    nlinarith [abs_nonneg (Z i j)]
  calc ∑ i, ∑ j, Z i j ^ 2 ≤ ∑ i, ∑ j, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (n * n : ℝ) := by simp

/-- **The `hcover` hypothesis, discharged.**  The initial ellipsoid `(initShape (n*n), 0)` covers
the strict threshold body at every rational threshold and every rational slack. -/
theorem initEll_covers_strictBody {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (t εr : ℚ) :
    ∀ z, QMCLeafB.AnswerProducer.StrictBody A t εr z →
      Ell (castM (initShape (n * n))) (0 : Fin (n * n) → ℝ) z := by
  intro z hz
  refine ell_initShape (Nat.mul_pos hn hn) ?_
  have h := sum_sq_le_of_strictBody hz
  rw [Nat.cast_mul]
  exact h

/-- **The starting potential of the strict-body loop**: `Φ₀ = (√N)^N`. -/
theorem volPot_initShape (N : ℕ) (hN : 0 < N) :
    volPot N (initShape N) = (Real.sqrt (N : ℝ)) ^ N := by
  rw [initShape, volPot_initShapeOf N (M := (N : ℚ)) (by exact_mod_cast hN)]
  push_cast
  rfl

/-! ## 2.  Flat coordinates: `unflat`, the flat Euclidean ball, and the trace/Frobenius bridge -/

/-- The inverse of `AnswerProducer.flat`: flattening is the bijection
`Fin n × Fin n ≃ Fin (n*n)`. -/
noncomputable def unflat {n : ℕ} (z : Fin (n * n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => z (finProdFinEquiv (i, j))

theorem flat_unflat {n : ℕ} (z : Fin (n * n) → ℝ) :
    QMCLeafB.AnswerProducer.flat (unflat z) = z := by
  funext k
  show z (finProdFinEquiv (finProdFinEquiv.symm k)) = z k
  rw [Equiv.apply_symm_apply]

theorem unflat_flat {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    unflat (QMCLeafB.AnswerProducer.flat X) = X := by
  ext i j
  show QMCLeafB.AnswerProducer.flat X (finProdFinEquiv (i, j)) = X i j
  simp [QMCLeafB.AnswerProducer.flat, Equiv.symm_apply_apply]

theorem flat_sub {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.AnswerProducer.flat (X - Y)
      = QMCLeafB.AnswerProducer.flat X - QMCLeafB.AnswerProducer.flat Y := by
  funext k
  simp [QMCLeafB.AnswerProducer.flat]

/-- **The Euclidean ball in flat coordinates**, written with the sum of squares so that no norm
instance is involved (`= BallFloor.eucBallAt`, whose membership form is
`BallFloor.mem_eucBallAt_iff`). -/
def eucBallF {N : ℕ} (u : Fin N → ℝ) (r : ℝ) : Set (Fin N → ℝ) :=
  {z | ∑ i, (z i - u i) ^ 2 ≤ r ^ 2}

/-- `frob A Z` **is** `tr (A Z)` on the feasible set: the trace of `A * Z` sums `Aᵢⱼ Zⱼᵢ` and
`Z` is symmetric.  This is the dictionary between `BallFloor`'s Frobenius ledger and
`AnswerProducer.StrictBody`'s trace ledger. -/
theorem frob_eq_trace {n : ℕ} {A Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : QMCLeafB.AnswerProducer.IsUnitDiagPSD Z) :
    QMCLeafB.BallFloor.frob A Z = (A * Z).trace := by
  have hsym : ∀ i j : Fin n, Z j i = Z i j := by
    intro i j
    have h := QMCLeafB.AnswerProducer.transpose_eq_of_posSemidef hZ.1
    have h2 := congrFun (congrFun h j) i
    simpa [Matrix.transpose_apply] using h2.symm
  simp only [QMCLeafB.BallFloor.frob, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [hsym i j]

/-- **`StrictBody` at tolerance `0` sits in `BallFloor`'s relaxation at any tolerance** — the
inclusion that lets the ball floor act on the refutation body. -/
theorem strictBody_relaxBodyLE {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {t εr : ℚ} {δ : ℝ}
    (hδ : 0 ≤ δ) {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : QMCLeafB.AnswerProducer.IsUnitDiagPSD Z)
    (htr : (A * Z).trace ≤ (t : ℝ) - (εr : ℝ)) :
    QMCLeafB.BallFloor.relaxBodyLE A ((t : ℝ) - (εr : ℝ)) δ Z :=
  QMCLeafB.BallFloor.bodyLE_subset_relaxBodyLE hδ ⟨hZ.1, hZ.2⟩
    (by rw [frob_eq_trace hZ]; exact htr)

/-- **The ball floor's half 1, restated in flat coordinates.**  A point `X₀` of the half-tolerance
relaxation carries the whole Euclidean ball of radius `δ/(8(c_A+1))` inside the full-tolerance
relaxation — `BallFloor.ball_subset_relaxBodyLE`, transported through `flat`/`unflat`. -/
theorem relaxBall_of_ballFloor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ cA : ℝ}
    (hδ : 0 < δ) (hcA : 0 ≤ cA) (hAsum : ∑ i, ∑ j, |A i j| ≤ cA)
    {Z : Matrix (Fin n) (Fin n) ℝ}
    (h₀ : QMCLeafB.BallFloor.relaxBodyLE A u (δ / 2) Z) :
    ∀ z, eucBallF (QMCLeafB.AnswerProducer.flat Z) (δ / (8 * (cA + 1))) z →
      QMCLeafB.BallFloor.relaxBodyLE A u δ (unflat z) := by
  intro z hz
  have hfn : QMCLeafB.BallFloor.frobNormSq (unflat z - Z)
      = ∑ k : Fin (n * n), (QMCLeafB.AnswerProducer.flat (unflat z - Z)) k ^ 2 := by
    simp only [QMCLeafB.BallFloor.frobNormSq]
    exact (sum_sq_flat (unflat z - Z)).symm
  have hkey : QMCLeafB.BallFloor.frobNormSq (unflat z - Z)
      ≤ (δ / (8 * (cA + 1))) ^ 2 := by
    rw [hfn]
    refine le_trans (le_of_eq ?_) hz
    exact Finset.sum_congr rfl fun k _ => by simp [flat_sub, flat_unflat]
  exact QMCLeafB.BallFloor.ball_subset_relaxBodyLE hδ hcA hAsum h₀ hkey

/-! ## 3.  The run at a fixed, closed-form round count

`EngineIterates.engine_run` and `engine_run_margin` produce `∃ K`.  A program cannot search for
`K`; it runs a number of rounds it computed in advance.  The halving form
(`Aat_vol_below_of_halving`) has no logarithms: `m` halves the potential factor and `K` clears
`Φ₀/ε`, and the bound holds at `T₀ = K * m`.  The next two theorems carry the *containment*
invariant along with the potential at that same explicit round count. -/

/-- **The run's invariant at the explicit round `K·m`** (cut depths `ρ` given directly). -/
theorem body_containment_at_halving
    {N : ℕ} (hN : 2 ≤ N) {A0 : Matrix (Fin N) (Fin N) ℚ} {cd : ℕ → CutData N}
    (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat N A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (a0 : Fin N → ℝ) (body : (Fin N → ℝ) → Prop)
    (hcover : ∀ z, body z → Ell (castM A0) a0 z)
    (hcut : ∀ k z, body z →
      -(((cd k).rho : ℝ) * sqrtSigmaR (cutCR cd k) (cutPR cd k)) ≤
        cutCR cd k ⬝ᵥ (z - Cat N a0 cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    {m K : ℕ} (hm : (Real.sqrt (rho0R N (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    {ε : ℝ} (hK : volPot N A0 * (1 / 2) ^ K ≤ ε) :
    (∀ z, body z → Ell (castM (Aat N A0 cd (K * m))) (Cat N a0 cd (K * m)) z) ∧
      volPot N (Aat N A0 cd (K * m)) ≤ ε :=
  ⟨body_containment hN hA0 hwit hρ hcne a0 body hcover hcut (K * m),
    Aat_vol_below_of_halving hN hA0 hwit hρ hcne hρmax hle hm hK⟩

/-- **The same at the oracle's absolute margins.**  `brick-sep-oracle` reports a rational normal
`c k` together with a *positive* absolute margin `δ k` (how far the violated halfspace misses the
centre); the engine records the cut at a rational normalised depth `ρ k` with `δ² ≤ ρ²σ`.  This is
`EngineIterates.engine_run_margin`'s translation, carried to the explicit round count. -/
theorem body_containment_at_halving_margin
    {N : ℕ} (hN : 2 ≤ N) {A0 : Matrix (Fin N) (Fin N) ℚ} {cd : ℕ → CutData N}
    (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat N A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (a0 : Fin N → ℝ) (body : (Fin N → ℝ) → Prop)
    (hcover : ∀ z, body z → Ell (castM A0) a0 z)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, 0 ≤ δ k)
    (hcheck : ∀ k, (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k z, body z → -(((δ k : ℚ)) : ℝ) ≤ cutCR cd k ⬝ᵥ (z - Cat N a0 cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    {m K : ℕ} (hm : (Real.sqrt (rho0R N (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    {ε : ℝ} (hK : volPot N A0 * (1 / 2) ^ K ≤ ε) :
    (∀ z, body z → Ell (castM (Aat N A0 cd (K * m))) (Cat N a0 cd (K * m)) z) ∧
      volPot N (Aat N A0 cd (K * m)) ≤ ε := by
  have hcut : ∀ k z, body z →
      -(((cd k).rho : ℝ) * sqrtSigmaR (cutCR cd k) (cutPR cd k)) ≤
        cutCR cd k ⬝ᵥ (z - Cat N a0 cd k) := by
    intro k z hz
    have hσR : 0 < sigmaR (cutCR cd k) (cutPR cd k) :=
      sigmaR_pos (Aat_cast_posDef hN hA0 hwit hρ hcne k) (cast_witness hwit k)
        (cast_normal_ne (hcne k))
    have hδle : (((δ k : ℚ)) : ℝ)
        ≤ ((cd k).rho : ℝ) * Real.sqrt ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ) :=
      margin_le_of_sq_check (hδ0 k) (hρ k) (sigmaQ_pos_of_cast hσR).le (hcheck k)
    have hσeq : ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ) = sigmaR (cutCR cd k) (cutPR cd k) :=
      cast_sigmaQ (cd k).c (cd k).p
    rw [hσeq] at hδle
    exact le_trans (neg_le_neg hδle) (hcutδ k z hz)
  exact body_containment_at_halving hN hA0 hwit hρ hcne a0 body hcover hcut hρmax hle hm hK

/-! ## 4.  The refuted verdict at the explicit round count

Now the boundary objects meet.  `A0 = initShapeOf (n*n) M` and `a0 = 0` come from §1; the run is
the explicit `T₀ = K·m` of §3; the ball floor's two halves are `hball` (a strict-body point carries
a ball into the relaxation `W`) and `BallFloor.pow_two_mul_det_le_one_of_ball_subset_Ell` (a ball
in the ellipsoid floors the determinant), which is *derived* here rather than assumed. -/

/-- **The refuted branch, at a static round count, with the initial ellipsoid constructed.**

`W` is the ball-carrying relaxation the engine runs on — **not** `StrictBody`: see the module
note.  For the campaign's parameters `W` is `fun z => BallFloor.relaxBodyLE A (t-εr) δ (unflat z)`
and `hball` is `relaxBall_of_ballFloor` (see `strictBody_refuted`).

Hypotheses: `hWbound` (the relaxation's norm bound, giving `M`); `hwit`/`hρ`/`hcne` (the recorded
cut sequence); `hδ0`/`hcheck`/`hcutδ` (the separation oracle's contract on `W`); `hρmax`/`hle`/`hm`
(the shallow regime and its halving time); `hr`; `hK` (`K` clears `Φ₀/r^{n²}` strictly);
`hball` (ball-floor half 1).

Conclusion: no unit-diagonal semidefinite `Z` has `tr (A Z) < t − εr` — verbatim the second clause
of `FinishLine.SoundεOnBracket`. -/
theorem strictBody_refuted_at_halving
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (t εr : ℚ)
    (M : ℚ) (hM : 0 < M)
    (W : (Fin (n * n) → ℝ) → Prop)
    (hWbound : ∀ z, W z → ∑ i, z i ^ 2 ≤ (M : ℝ))
    (cd : ℕ → CutData (n * n))
    (hwit : ∀ k, Aat (n * n) (initShapeOf (n * n) M) cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, 0 ≤ δ k)
    (hcheck : ∀ k, (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k z, W z →
      -(((δ k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (n * n) (0 : Fin (n * n) → ℝ) cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    {m K : ℕ} (hm : (Real.sqrt (rho0R (n * n) (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
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
    body_containment_at_halving_margin (N := n * n) hn' hA0 hwit hρ hcne
      (0 : Fin (n * n) → ℝ) W (fun z hz => ell_initShapeOf hM (hWbound z hz))
      hδ0 hcheck hcutδ hρmax hle hm le_rfl
  have hKpd : (castM (Aat (n * n) (initShapeOf (n * n) M) cd (K * m))).PosDef :=
    Aat_cast_posDef hn' hA0 hwit hρ hcne (K * m)
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

/-! ## 5.  The fully wired version: the ball floor of `Check_ball_floor` plugged in

The last free hypothesis of §4 is `hball`.  Taking the relaxation to be
`W z = BallFloor.relaxBodyLE A (t − εr) δ (unflat z)`, `hball` is `relaxBall_of_ballFloor`
composed with `strictBody_relaxBodyLE`, and the ball radius becomes the campaign's own
`ballFloorRadius δ cA = δ/(8(c_A+1))`.  What remains is only the *norm bound* `hWbound` on the
relaxation (the initial ellipsoid's radius), the oracle contract, and the closed-form round
count. -/

/-- **The refuted verdict with no ball hypothesis left.**  `W` is the flat image of
`BallFloor.relaxBodyLE`; the only quantitative inputs are the ball-floor radius
`r = δ/(8(c_A+1))`, the ledger constant `cA ≥ ∑ᵢⱼ|Aᵢⱼ|`, and the relaxation's norm bound `M`. -/
theorem strictBody_refuted
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (t εr : ℚ)
    (δq cAq : ℚ) (hδq : 0 < δq) (hcAq : 0 ≤ cAq)
    (hAsum : ∑ i, ∑ j, |A i j| ≤ (cAq : ℝ))
    (M : ℚ) (hM : 0 < M)
    (hWbound : ∀ z : Fin (n * n) → ℝ,
      QMCLeafB.BallFloor.relaxBodyLE A ((t : ℝ) - (εr : ℝ)) (δq : ℝ) (unflat z) →
      ∑ i, z i ^ 2 ≤ (M : ℝ))
    (cd : ℕ → CutData (n * n))
    (hwit : ∀ k, Aat (n * n) (initShapeOf (n * n) M) cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, 0 ≤ δ k)
    (hcheck : ∀ k, (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k z,
      QMCLeafB.BallFloor.relaxBodyLE A ((t : ℝ) - (εr : ℝ)) (δq : ℝ) (unflat z) →
      -(((δ k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (n * n) (0 : Fin (n * n) → ℝ) cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    {m K : ℕ} (hm : (Real.sqrt (rho0R (n * n) (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (hK : volPot (n * n) (initShapeOf (n * n) M) * (1 / 2) ^ K
      < ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n)) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace := by
  have hδR : (0 : ℝ) < (δq : ℝ) := by exact_mod_cast hδq
  have hcAR : (0 : ℝ) ≤ (cAq : ℝ) := by exact_mod_cast hcAq
  have hδ8 : (0 : ℝ) < (δq : ℝ) / (8 * ((cAq : ℝ) + 1)) := by positivity
  refine strictBody_refuted_at_halving hn A t εr M hM
    (fun z => QMCLeafB.BallFloor.relaxBodyLE A ((t : ℝ) - (εr : ℝ)) (δq : ℝ) (unflat z))
    hWbound cd hwit hρ hcne hδ0 hcheck hcutδ hρmax hle hm hδ8 hK ?_
  intro u hu
  obtain ⟨Z, hZ, htr, rfl⟩ := hu
  exact relaxBall_of_ballFloor (u := (t : ℝ) - (εr : ℝ)) hδR hcAR hAsum
    (strictBody_relaxBodyLE (δ := (δq : ℝ) / 2) (by positivity) hZ htr)

/-! ## 5.1  Closing the last quantitative hypothesis: a norm-bounded relaxation

`strictBody_refuted` still assumes `hWbound`, the relaxation's norm bound, because
`BallFloor.relaxBodyLE` alone does **not** bound the norm: it constrains only `Xᵢᵢ` and the
quadratic form, and an antisymmetric part is invisible to `xᵀ X x`.  Adding the norm bound to the
relaxation costs nothing — the engine's cut contract and cover are then required on a *smaller*
set, and a ball around a strict-body point still lands inside, because a strict-body point has
norm-squared at most `n²` and the ball has radius `r`.

So `W z := relaxBodyLE A (t−εr) δ (unflat z) ∧ ∑ zᵢ² ≤ M`, and with
`M ≥ 2(n² + r²)` both `hWbound` and `hball` are *proved*, not assumed. -/

/-- The norm-bounded, ball-carrying relaxation of the threshold body, in flat coordinates. -/
def relaxBall {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u δ M : ℝ) : Set (Fin (n * n) → ℝ) :=
  {z | QMCLeafB.BallFloor.relaxBodyLE A u δ (unflat z) ∧ ∑ i, z i ^ 2 ≤ M}

/-- The norm bound of `relaxBall`, by construction. -/
theorem relaxBall_norm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ M : ℝ}
    {z : Fin (n * n) → ℝ} (hz : z ∈ relaxBall A u δ M) : ∑ i, z i ^ 2 ≤ M := hz.2

/-- A ball of radius `r` around a strict-body point lands in `relaxBall A (t−εr) δ M` as soon as
`M ≥ 2(n² + r²)`. -/
theorem strictBody_ball_relaxBall {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {t εr : ℚ}
    {δq : ℚ} (hδ : 0 < (δq : ℝ)) {cA : ℝ} (hcA : 0 ≤ cA)
    (hAsum : ∑ i, ∑ j, |A i j| ≤ cA) {M : ℝ}
    (hM : 2 * (((n : ℝ)) ^ 2 + ((δq : ℝ) / (8 * (cA + 1))) ^ 2) ≤ M)
    {u : Fin (n * n) → ℝ} (hu : QMCLeafB.AnswerProducer.StrictBody A t εr u) :
    eucBallF u ((δq : ℝ) / (8 * (cA + 1))) ⊆ relaxBall A ((t : ℝ) - (εr : ℝ)) (δq : ℝ) M := by
  intro z hz
  obtain ⟨Z, hZ, htr, rfl⟩ := hu
  refine ⟨?_, ?_⟩
  · exact relaxBall_of_ballFloor (u := (t : ℝ) - (εr : ℝ)) hδ hcA hAsum
      (strictBody_relaxBodyLE (δ := (δq : ℝ) / 2) (by positivity) hZ htr) z hz
  · have hun : ∑ i, (QMCLeafB.AnswerProducer.flat Z) i ^ 2 ≤ (n : ℝ) * (n : ℝ) := by
      exact sum_sq_le_of_strictBody ⟨Z, hZ, htr, rfl⟩
    have hterm : ∀ i : Fin (n * n),
        (z i) ^ 2 ≤ 2 * (z i - QMCLeafB.AnswerProducer.flat Z i) ^ 2
          + 2 * (QMCLeafB.AnswerProducer.flat Z i) ^ 2 := by
      intro i
      nlinarith [sq_nonneg ((z i - QMCLeafB.AnswerProducer.flat Z i)
        - QMCLeafB.AnswerProducer.flat Z i)]
    have hsplit : ∑ i, (2 * (z i - QMCLeafB.AnswerProducer.flat Z i) ^ 2
        + 2 * (QMCLeafB.AnswerProducer.flat Z i) ^ 2)
        = 2 * ∑ i, (z i - QMCLeafB.AnswerProducer.flat Z i) ^ 2
          + 2 * ∑ i, (QMCLeafB.AnswerProducer.flat Z i) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hz' : ∑ i, (z i - QMCLeafB.AnswerProducer.flat Z i) ^ 2
        ≤ ((δq : ℝ) / (8 * (cA + 1))) ^ 2 := hz
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [hsplit] at hsum
    linarith

/-- **The refuted verdict, fully wired.**  For the norm-bounded relaxation `relaxBall`:

* the initial ellipsoid `initShapeOf (n*n) M = M⁻¹ • 1` covers `relaxBall` (`ell_initShapeOf`);
* the run of exactly `K·m` rounds keeps `relaxBall` inside `Ell (Aat (K·m)) (Cat (K·m))`
  (`body_containment_at_halving_margin`);
* every strict-body point carries a ball of the campaign's radius `δ/(8(c_A+1))` into `relaxBall`
  (`strictBody_ball_relaxBall`);
* a ball in the ellipsoid floors the determinant (`BallFloor.pow_two_mul_det_le_one_of_ball_subset_Ell`).

Left free: the recorded cut sequence with its rational witness relation, the separation oracle's
absolute-margin contract on `relaxBall`, the shallow-regime halving time `m`, and the strict round
count condition `Φ₀·2^{-K} < r^{n²}`.  Nothing else. -/
theorem strictBody_refuted_final
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (t εr : ℚ)
    (δq cAq : ℚ) (hδq : 0 < δq) (hcAq : 0 ≤ cAq)
    (hAsum : ∑ i, ∑ j, |A i j| ≤ (cAq : ℝ))
    (M : ℚ) (hM : 0 < M)
    (hMbig : 2 * (((n : ℝ)) ^ 2 + ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ 2) ≤ (M : ℝ))
    (cd : ℕ → CutData (n * n))
    (hwit : ∀ k, Aat (n * n) (initShapeOf (n * n) M) cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, 0 ≤ δ k)
    (hcheck : ∀ k, (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k z, z ∈ relaxBall A ((t : ℝ) - (εr : ℝ)) (δq : ℝ) (M : ℝ) →
      -(((δ k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (n * n) (0 : Fin (n * n) → ℝ) cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    {m K : ℕ} (hm : (Real.sqrt (rho0R (n * n) (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (hK : volPot (n * n) (initShapeOf (n * n) M) * (1 / 2) ^ K
      < ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n)) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace := by
  have hδR : (0 : ℝ) < (δq : ℝ) := by exact_mod_cast hδq
  have hcAR : (0 : ℝ) ≤ (cAq : ℝ) := by exact_mod_cast hcAq
  have hδ8 : (0 : ℝ) < (δq : ℝ) / (8 * ((cAq : ℝ) + 1)) := by positivity
  refine strictBody_refuted_at_halving hn A t εr M hM
    (relaxBall A ((t : ℝ) - (εr : ℝ)) (δq : ℝ) (M : ℝ)) (fun z hz => hz.2)
    cd hwit hρ hcne hδ0 hcheck hcutδ hρmax hle hm hδ8 hK ?_
  intro u hu
  exact strictBody_ball_relaxBall hδR hcAR hAsum hMbig hu

/-! ## 5.2  The radius constant `M`, made explicit

`strictBody_refuted_final` takes the relaxation's radius `M` as a rational with the side condition
`M ≥ 2(n² + r²)`.  That side condition is satisfiable with an explicit rational: since the ball
radius `r = δ/(8(c_A+1))` never exceeds `δ` (as `cA ≥ 0`), the choice `M = 2n² + 2δ²` works.  Then
`Φ₀ = (√M)^{n²}` by `volPot_initShapeOf`, so the round count `K` is the only number left to the
ledger. -/

/-- **The explicit radius.**  `M = 2n² + 2δ²` is positive and dominates `2(n² + r²)` for
`r = δ/(8(c_A+1))`, `c_A ≥ 0`. -/
theorem exists_M {n : ℕ} (hn : 1 ≤ n) {δq : ℚ} (hδq : 0 < δq) {cA : ℚ} (hcA : 0 ≤ cA) :
    0 < 2 * (n : ℚ) ^ 2 + 2 * δq ^ 2 ∧
      2 * (((n : ℝ)) ^ 2 + ((δq : ℝ) / (8 * ((cA : ℝ) + 1))) ^ 2)
        ≤ ((2 * (n : ℚ) ^ 2 + 2 * δq ^ 2 : ℚ) : ℝ) := by
  have hcAR : (0 : ℝ) ≤ (cA : ℝ) := by exact_mod_cast hcA
  have hδR : (0 : ℝ) < (δq : ℝ) := by exact_mod_cast hδq
  have hr0 : (0 : ℝ) ≤ (δq : ℝ) / (8 * ((cA : ℝ) + 1)) := by positivity
  have hrδ : (δq : ℝ) / (8 * ((cA : ℝ) + 1)) ≤ (δq : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsq : ((δq : ℝ) / (8 * ((cA : ℝ) + 1))) ^ 2 ≤ ((δq : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hr0 hrδ 2
  constructor
  · positivity
  · push_cast
    nlinarith

/-- **The refuted verdict with the radius instantiated.**  Same as `strictBody_refuted_final` with
`M = 2n² + 2δ²`, so the only arithmetic input is the round count condition
`Φ₀·2^{-K} < r^{n²}` (whose `Φ₀` is `(√M)^{n²}` by `volPot_initShapeOf`). -/
theorem strictBody_refuted_concrete
    {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (t εr : ℚ)
    (δq cAq : ℚ) (hδq : 0 < δq) (hcAq : 0 ≤ cAq)
    (hAsum : ∑ i, ∑ j, |A i j| ≤ (cAq : ℝ))
    (cd : ℕ → CutData (n * n))
    (hwit : ∀ k, Aat (n * n) (initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2)) cd k
      *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, 0 ≤ δ k)
    (hcheck : ∀ k, (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k z, z ∈ relaxBall A ((t : ℝ) - (εr : ℝ)) (δq : ℝ)
        ((2 * (n : ℚ) ^ 2 + 2 * δq ^ 2 : ℚ) : ℝ) →
      -(((δ k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (n * n) (0 : Fin (n * n) → ℝ) cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    {m K : ℕ} (hm : (Real.sqrt (rho0R (n * n) (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (hK : volPot (n * n) (initShapeOf (n * n) (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2)) * (1 / 2) ^ K
      < ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n)) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace := by
  obtain ⟨hMpos, hMbig⟩ := exists_M (n := n) (by omega) hδq hcAq
  exact strictBody_refuted_final hn A t εr δq cAq hδq hcAq hAsum
    (2 * (n : ℚ) ^ 2 + 2 * δq ^ 2) hMpos hMbig cd hwit hρ hcne hδ0 hcheck hcutδ
    hρmax hle hm hK

/-! ## 6.  The two existence lemmas the ledger quotes -/

/-- **A halving time exists** once the potential factor contracts. -/
theorem exists_halving_time {N : ℕ} {ρmax : ℝ} (h : 1 < rho0R N ρmax) :
    ∃ m : ℕ, (Real.sqrt (rho0R N ρmax))⁻¹ ^ m ≤ 1 / 2 := by
  have hspos : (0 : ℝ) < rho0R N ρmax := lt_trans one_pos h
  have hs : 1 < Real.sqrt (rho0R N ρmax) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using h
  have hc1 : (Real.sqrt (rho0R N ρmax))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (x := (1 : ℝ) / 2) (by norm_num) hc1
  exact ⟨m, le_of_lt hm⟩

/-- **A round count clearing `Φ₀ / r^{n²}` exists** whenever the starting potential is finite and
the floor radius positive. -/
theorem exists_rounds {Φ₀ : ℝ} (hΦ : 0 ≤ Φ₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, Φ₀ * (1 / 2) ^ K < ε := by
  rcases eq_or_lt_of_le hΦ with h0 | hpos
  · exact ⟨0, by simpa [← h0] using hε⟩
  · have hlt : (1 / 2 : ℝ) < 1 := by norm_num
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (x := ε / Φ₀) (div_pos hε hpos) hlt
    exact ⟨K, by
      calc Φ₀ * (1 / 2) ^ K < Φ₀ * (ε / Φ₀) := mul_lt_mul_of_pos_left hK hpos
        _ = ε := by field_simp⟩

end QMCLeafB.Boundary

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.Boundary.castM_initShapeOf
#print axioms QMCLeafB.Boundary.initShapeOf_cast_posDef
#print axioms QMCLeafB.Boundary.ell_initShapeOf
#print axioms QMCLeafB.Boundary.volPot_initShapeOf
#print axioms QMCLeafB.Boundary.initShape_cast_posDef
#print axioms QMCLeafB.Boundary.sum_sq_flat
#print axioms QMCLeafB.Boundary.sum_sq_le_of_strictBody
#print axioms QMCLeafB.Boundary.initEll_covers_strictBody
#print axioms QMCLeafB.Boundary.volPot_initShape
#print axioms QMCLeafB.Boundary.flat_unflat
#print axioms QMCLeafB.Boundary.unflat_flat
#print axioms QMCLeafB.Boundary.frob_eq_trace
#print axioms QMCLeafB.Boundary.strictBody_relaxBodyLE
#print axioms QMCLeafB.Boundary.relaxBall_of_ballFloor
#print axioms QMCLeafB.Boundary.body_containment_at_halving
#print axioms QMCLeafB.Boundary.body_containment_at_halving_margin
#print axioms QMCLeafB.Boundary.strictBody_refuted_at_halving
#print axioms QMCLeafB.Boundary.strictBody_refuted
#print axioms QMCLeafB.Boundary.relaxBall_norm
#print axioms QMCLeafB.Boundary.strictBody_ball_relaxBall
#print axioms QMCLeafB.Boundary.strictBody_refuted_final
#print axioms QMCLeafB.Boundary.exists_M
#print axioms QMCLeafB.Boundary.strictBody_refuted_concrete
#print axioms QMCLeafB.Boundary.exists_halving_time
#print axioms QMCLeafB.Boundary.exists_rounds


