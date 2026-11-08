-- Prove2me | Definitions.Def_QMCLeafB_AnswerProducer
-- name    : QMCLeafB_AnswerProducer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T16:04:19.195975+00:00
-- url     : https://prove2.me/theorems/478272e8-5c7d-45d9-94cf-eef988968dc2
-- title:
--   Engine contract with slack (Answerε and bisection driver)
-- statement:
--   The slack engine's contract $\mathrm{Answer}_{\varepsilon}(A,t,\varepsilon_w,\varepsilon_r)$ with tolerance $\varepsilon_w$ on the witness trace and $\varepsilon_r$ on the refutation, its bisection driver and thirteen-step closing bound $S-L \le R/32768 + (\varepsilon_w+\varepsilon_r)/4$ for $W/10000$ budget.
-- source:
--   QMC leaf B, answer-producer brick (phase 4), https://prove2.me

/-
# leaf B phase 4 — brick `answer-producer`

The fixed-threshold engine's **contract**.  `ThresholdDriver` (phase 3) turns a per-threshold
answer `Answer A t` into leaf B's rational lower value.  This file supplies the two seams that
`Answer` leaves open, and nothing else:

## 1.  The answer must be allowed to be *approximate* — on both sides

`ThresholdDriver.Answer A t` demands an **exact** decision at every rational threshold `t`:

* `.feasible X` needs `tr (A X) ≤ t` with `X` exactly unit-diagonal and exactly PSD;
* `.infeasible` needs `t ≤ tr (A Z)` for **every** feasible `Z`.

Neither is computable by an ellipsoid engine.  The engine's separation oracle works with
*positive margins* (`SepOracle.OkReport`), the rounding step (`RoundingOut.exists_displayPair`)
produces a rational point whose trace overshoots `t` by a rounding slack, and the volume-potential
termination (`EngineIterates.engine_run`) can only refute the body with a *slack*: all it proves is
that no feasible point has `tr (A Z) ≤ t - εr`.  So the producer's honest output type is

    Answerε A t εw εr  =  .witness X ... (tr (A X) ≤ t + εw)  |  .refuted (... t - εr ≤ tr (A Z))

with `εw` the primal (rounding) slack and `εr` the refutation (termination radius) slack.  §1
below defines it, proves that the exact type is the special case `εw = εr = 0` (`Answer` is
recovered verbatim, both ways), and records monotonicity in the threshold.

## 2.  A slack answer still wins leaf B, for an explicit precision budget

§3 re-runs `ThresholdDriver`'s thirteen-call bisection on the slack type.  The bracket keeps a
refutation only down to `lo - εr` and a witness only up to `hi + εw`, and the two errors enter the
sandwich linearly:

    L := (V A - hi - εw)/4  ⟹  L ≤ S  and  S - L ≤ (hi - lo)/4 + (εw + εr)/4.

After thirteen steps `(hi - lo)/4 = R/2^13/4 = R/32768 = W/16384`, so

    εw + εr ≤ W/7500  ⟹  S - L ≤ W/10000      (W = ∑ weights),

which is the **budget the engine bricks have to meet**; it is the quantitative content of
"the producer's termination condition intersects the driver's requirement".  Taking
`εw = εr = 0` recovers `ThresholdDriver.leafB_threshold_driver_wMatrix` verbatim.

## 3.  Where the refuted branch comes from: the ball floor

§2 shows that the refutation is *delivered by geometry*, not assumed.  `EngineIterates.engine_run`
gives a run length `K` at which the threshold body sits inside the ellipsoid
`Ell A_K a_K = {z | (z - a_K)ᵀ A_K (z - a_K) ≤ 1}` and the volume potential
`Φ = 1/√(det A_K)` is below any `ε`.  If the body contains a Euclidean ball of radius `r` around
each of its points — which is what the oracle's margins give (`brick-ball-floor`, half 1) — then
the ellipsoid's own volume bounds the potential below: `r^d ≤ Φ` (`brick-ball-floor`, half 2, the
ellipsoid volume identity).  Choosing the termination radius `r` with `r^d > Φ_K` therefore
**excludes** the body: `refute_of_squeezed`.  The floor enters as the single hypothesis

    hfloor : u ∈ body ⟹ r^(2d) · det A_K ≤ 1      (d = n², the flattened matrix dimension)

which is definitionally the composite of `brick-ball-floor`'s two halves; `floor_of_ball`
records that composition so the interface is not a black box.

## Index

| statement | what it says |
|---|---|
| `Answer` | the exact per-threshold answer (`ThresholdDriver.Answer`, restated) |
| `Answerε` | the producer's answer with primal slack `εw` and refutation slack `εr` |
| `Answer.toSlack`, `Answerε.toExact` | `Answerε A t 0 0` **is** `Answer A t`, both ways |
| `lower_of_witness`, `upper_of_refuted` | each constructor gives one side of the sandwich |
| `Ell`, `eucBall`, `volPot` | the ellipsoid, the ball, the volume potential (arbitrary finite index type) |
| `rpow_le_volPot` | `eucBall u r ⊆ Ell K a ⟹ r^(2d)·det K ≤ 1` ⟹ `r^d ≤ Φ` (ball-floor, half 2) |
| `floor_of_ball` | composition of the two halves of the ball floor on a body |
| `empty_of_floor` | a body with the floor and `Φ < r^d` has no points (the termination condition) |
| `flat`, `StrictBody` | the matrix body, flattened onto `Fin (n * n)` |
| `refute_of_squeezed` | **the refuted constructor, delivered**: covering ellipsoid + floor + `Φ < r^d` ⟹ `t - εr ≤ tr (A Z)` on the whole feasible set |
| `Squeeze` | the engine's stopping datum, field by field an output of a compiled brick |
| `strictBody_subset_ell` | the body sits in the covering ellipsoid |
| `squeeze_of_engine` | **the interface**: containment + ball-floor half 1 + half 2 + `Φ < r^d` ⟹ `Squeeze` |
| `Squeeze.refute` | a squeeze is a refutation (driver's form) |
| `Squeeze.body_empty` | a squeeze excludes the body outright |
| `dual_refutes`, `answer_of_dual` | the certificate route to `.refuted` (no geometry) |
| `Outcome`, `Outcome.toAnswer` | the producer: witness or squeeze ⟹ `Answerε` |
| `Producer`, `Producer.answers` | a total producer answers every rational threshold |
| `Producer.ofExact`, `producer_zero` | the exact engine is a zero-slack producer; the contract is inhabited |
| `SlackBrack`, `step`, `iter`, `iter_width` | the slack bisection; width halves per call |
| `lower_bound`, `upper_bound`, `driver_bounds` | the two sides of the slack sandwich |
| `startBrack`, `startBrack_width` | the concrete start `lo = -R`, `hi = 0`, width `R` |
| `leafB_threshold_driver_slack` | thirteen calls: `0 ≤ Lq`, `Lq ≤ S`, `S - Lq ≤ R/32768 + (εw+εr)/4` |
| `leafB_threshold_driver_wMatrix_slack` | the same at `A = wMatrix G`: `W/16384 + (εw+εr)/4` |
| `leafB_threshold_driver_wMatrix_budget` | **`εw + εr ≤ W/7500 ⟹ S - Lq ≤ W/10000`** (the precision budget) |
| `leafB_threshold_driver_wMatrix_exact` | `εw = εr = 0` recovers `ThresholdDriver.leafB_threshold_driver_wMatrix` |

## What this file does *not* prove (honest inventory)

1. **The ball floor itself**: `brick-ball-floor`'s two halves — a positive-margin point carries a
   ball of radius `r(δ,n)` inside the body (`hball` of `squeeze_of_engine`), and the ellipsoid
   volume identity `eucBall u r ⊆ Ell K a ⟹ r^(2d)·det K ≤ 1` with constant `1` (`hvol` there).
   `squeeze_of_engine` composes them into the single hypothesis `Squeeze.floor`; nothing else in
   this file depends on the floor.
2. **The construction of `Squeeze`**: running `EngineIterates.engine_run` (containment
   `body_containment`, the potential `Aat_vol_le`, and the choice of a termination radius `r` with
   `r^d > Φ_K`) is `brick-engine-runtime`'s and the iterate core's job; `Squeeze` is exactly its
   output signature.
3. **The `.found` branch's rounding**: producing a rational unit-diagonal `GramCert`-verified `X`
   with `tr (A X) ≤ t + εw` is `RoundingOut.exists_displayPair` + `CertPSD` (phase 3); the file
   consumes it as the constructor's data.
4. **Nothing about runtime.**  No `PolyProgram`, no TM2: `brick-engine-runtime` wraps `Producer`
   into the value form.

So the four bricks compose as: `brick-ball-floor` → `Squeeze.floor`; engine core + `brick-engine-runtime`
→ `Squeeze`; `RoundingOut`/`CertPSD` → `Outcome.found`; this file → `Answerε`; §3/§4 → the leaf's
`L`.  The single number that ties them is `εw + εr ≤ W/7500`.

No `sorry`, no `axiom`; the only imports are Mathlib and the campaign's merged library.
-/
import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Matrix

namespace QMCLeafB.AnswerProducer

variable {n : ℕ}

/-! ## 0.  The campaign's definitions, copied verbatim

The file is self-contained (`import Mathlib` only) so that it compiles independently of the
workspace's current `Solutions` build.  These four definitions are copied verbatim from
`Definitions/Def_ModernConvex_Relaxations_SignRelaxations.lean`, and `V`,
`maxcut_objective_eq`, `transpose_eq_of_posSemidef`, `psd_trace_mul_nonneg` and
`trace_diagonal_mul_of_unitDiag` from the campaign's merged library `Solutions/MergeAll3_m8.lean`
(namespace `QMCLeafB`).  They are definitionally the campaign's objects, so the theorems below
transfer verbatim; `Check_answer_producer_wMatrix.lean` re-derives the graph-instance statement
against the real imports. -/

/-- `X = Xᵀ ⪰ 0` with `Xᵢᵢ = 1` (Ben-Tal–Nemirovski (4.3.15)). -/
def IsUnitDiagPSD (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.PosSemidef ∧ ∀ i, X i i = 1

/-- `¼ ∑ᵢ ∑ⱼ aᵢⱼ (1 − Xᵢⱼ)`, the relaxed MAXCUT objective (4.3.15). -/
noncomputable def maxcutRelaxationObjective (a : Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j, a i j * (1 - X i j)

/-- `v` is the optimal value of the semidefinite relaxation: the least upper bound of the relaxed
objective over the unit-diagonal semidefinite set. -/
def IsMaxcutSDPValue (a : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) : Prop :=
  IsLUB (maxcutRelaxationObjective a '' {X | IsUnitDiagPSD X}) v

/-- `V A = ∑ᵢ ∑ⱼ Aᵢⱼ`, twice the total edge weight of a symmetric weight matrix. -/
noncomputable def V (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j

theorem symm_of_transpose_eq {X : Matrix (Fin n) (Fin n) ℝ} (hX : Xᵀ = X) :
    ∀ i j, X j i = X i j :=
  fun i j => by simpa [Matrix.transpose_apply] using congrFun (congrFun hX i) j

theorem transpose_eq_of_posSemidef {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) :
    Xᵀ = X := by
  ext i j
  simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using
    congrFun (congrFun hX.1.eq i) j

/-- The relaxed objective in trace form: `(V A − tr (A X))/4` on symmetric `X`. -/
theorem maxcut_objective_eq (A X : Matrix (Fin n) (Fin n) ℝ) (hX : Xᵀ = X) :
    maxcutRelaxationObjective A X = (V A - (A * X).trace) / 4 := by
  have hsym := symm_of_transpose_eq hX
  have htrace : (A * X).trace = ∑ i, ∑ j, A i j * X i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym]
  rw [htrace, maxcutRelaxationObjective, V, Finset.mul_sum]
  have hterm : ∀ i, (1 / 4 : ℝ) * ∑ j, A i j * (1 - X i j)
      = (1 / 4 : ℝ) * ((∑ j, A i j) - ∑ j, A i j * X i j) := by
    intro i
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- The trace of a product of positive semidefinite matrices is nonnegative. -/
theorem psd_trace_mul_nonneg {M X : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (hX : X.PosSemidef) : 0 ≤ (M * X).trace := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  simp only [star_trivial]
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_nonneg fun k _ => ?_
  have hterm : ((M * vecMulVec (v k) (v k)).trace) = (v k) ⬝ᵥ (M *ᵥ (v k)) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, vecMulVec_apply,
      Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hterm]
  exact hM.dotProduct_mulVec_nonneg (v k)

/-- `(diagonal y * X).trace = ∑ᵢ yᵢ Xᵢᵢ`. -/
theorem trace_diagonal_mul (y : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    (diagonal y * X).trace = ∑ i, y i * X i i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]

theorem trace_diagonal_mul_of_unitDiag (y : Fin n → ℝ) {X : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i, X i i = 1) : (diagonal y * X).trace = ∑ i, y i := by
  rw [trace_diagonal_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [h i, mul_one]

/-! ## 1.  The exact answer type, and its two-sided slack relaxation -/

/-- **The engine's exact answer at a fixed rational threshold `t`** — verbatim the inductive
`QMCLeafB.ThresholdDriver.Answer`, restated here so that this file is a single self-contained
deliverable (the linkage is recorded in `Answer.toSlack`/`Answerε.toExact` and in the docstring of
`Answerε`: at `εw = εr = 0` the two types are the same). -/
inductive Answer (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) : Type where
  /-- a genuine feasible point below the threshold -/
  | feasible (X : Matrix (Fin n) (Fin n) ℝ)
      (hX : IsUnitDiagPSD X)
      (htr : (A * X).trace ≤ (t : ℝ))
  /-- the proof that the threshold body is empty -/
  | infeasible (hlb : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (t : ℝ) ≤ (A * Z).trace)

/-- **The producer's honest answer type.**  `εw` is the primal (rounding) slack: the witness is
exact as a *point* (unit-diagonal, semidefinite) but its trace overshoots `t` by at most `εw`.
`εr` is the refutation (termination radius) slack: the engine proves that no feasible point has
trace at most `t - εr`.  `Answer A t` is the case `εw = εr = 0`. -/
inductive Answerε (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) (εw εr : ℚ) : Type where
  /-- a feasible point whose trace overshoots the threshold by at most `εw` -/
  | witness (X : Matrix (Fin n) (Fin n) ℝ)
      (hX : IsUnitDiagPSD X)
      (htr : (A * X).trace ≤ (t : ℝ) + (εw : ℝ))
  /-- every feasible point has trace at least `t - εr` -/
  | refuted (hlb : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace)

/-- The exact answer is a slack answer with zero slack. -/
def Answer.toSlack {A : Matrix (Fin n) (Fin n) ℝ} {t : ℚ} :
    Answer A t → Answerε A t 0 0
  | .feasible X hX htr => .witness X hX (by simpa using htr)
  | .infeasible hlb => .refuted (fun Z hZ => by simpa using hlb Z hZ)

/-- A slack answer with zero slack is an exact answer. -/
def Answerε.toExact {A : Matrix (Fin n) (Fin n) ℝ} {t : ℚ} :
    Answerε A t 0 0 → Answer A t
  | .witness X hX htr => .feasible X hX (by simpa using htr)
  | .refuted hlb => .infeasible (fun Z hZ => by simpa using hlb Z hZ)

/-- A witness at `t` is a witness at every larger threshold. -/
theorem Answerε.witness_mono {A : Matrix (Fin n) (Fin n) ℝ} {t t' : ℚ} {εw εr : ℚ}
    (htt : t ≤ t') {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsUnitDiagPSD X)
    (htr : (A * X).trace ≤ (t : ℝ) + (εw : ℝ)) :
    (A * X).trace ≤ (t' : ℝ) + (εw : ℝ) := by
  have : (t : ℝ) ≤ (t' : ℝ) := by exact_mod_cast htt
  linarith

/-- A refutation at `t` is a refutation at every smaller threshold. -/
theorem Answerε.refuted_mono {A : Matrix (Fin n) (Fin n) ℝ} {t t' : ℚ} {εw εr : ℚ}
    (htt : t' ≤ t)
    (h : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (t' : ℝ) - (εr : ℝ) ≤ (A * Z).trace := by
  intro Z hZ
  have hcast : (t' : ℝ) ≤ (t : ℝ) := by exact_mod_cast htt
  linarith [h Z hZ]

/-- **One side of the sandwich from a witness**: a feasible point whose trace is at most
`t + εw` already certifies the value `(V A - t - εw)/4`. -/
theorem lower_of_witness {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ} {t : ℚ} {εw : ℚ}
    (hS : IsMaxcutSDPValue A S)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsUnitDiagPSD X)
    (htr : (A * X).trace ≤ (t : ℝ) + (εw : ℝ)) :
    (V A - (t : ℝ) - (εw : ℝ)) / 4 ≤ S := by
  have hobj : maxcutRelaxationObjective A X
      = (V A - (A * X).trace) / 4 :=
    maxcut_objective_eq A X (transpose_eq_of_posSemidef hX.1)
  have hle : maxcutRelaxationObjective A X ≤ S :=
    hS.1 ⟨X, hX, rfl⟩
  rw [hobj] at hle
  linarith

/-- **One side of the sandwich from a refutation**: if every feasible point has trace at least
`t - εr`, the SDP value is at most `(V A - t)/4 + εr/4`. -/
theorem upper_of_refuted {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ} {t : ℚ} {εr : ℚ}
    (hS : IsMaxcutSDPValue A S)
    (h : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace) :
    S ≤ (V A - (t : ℝ)) / 4 + (εr : ℝ) / 4 := by
  refine hS.2 (Set.forall_mem_image.mpr fun Z hZ => ?_)
  rw [maxcut_objective_eq A Z (transpose_eq_of_posSemidef hZ.1)]
  have hh := h Z hZ
  have hV : V A = ∑ i, ∑ j, A i j := rfl
  rw [hV]
  linarith

/-! ## 2.  The ball floor, and how the refuted branch is *delivered*

`EngineIterates.engine_run` ends with a run length `K` at which the threshold body is inside the
ellipsoid `Ell A_K a_K` and the potential `Φ_K = 1/√(det A_K)` is below a target `ε`.  The floor
turns that into emptiness.  Everything in this section is pure `ℝ`-analysis on an arbitrary finite
index type `ι`; the matrix body is flattened onto `ι = Fin (n * n)` at the end. -/

section Geometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ellipsoid `{x | (x - a)ᵀ K (x - a) ≤ 1}` (`= EllipsoidStep.Ell`, generalized to an
arbitrary finite index type so that the matrix variable can be flattened). -/
noncomputable def Ell (K : Matrix ι ι ℝ) (a : ι → ℝ) : Set (ι → ℝ) :=
  {x | (x - a) ⬝ᵥ (K *ᵥ (x - a)) ≤ 1}

/-- The closed Euclidean ball of radius `r` around `u`. -/
noncomputable def eucBall (u : ι → ℝ) (r : ℝ) : Set (ι → ℝ) := {z | ‖z - u‖ ≤ r}

/-- The ellipsoid volume potential `Φ = 1/√(det K)` (`= EngineIterates.volPot`): the ellipsoid's
volume is `vol(unit ball) · Φ`. -/
noncomputable def volPot (K : Matrix ι ι ℝ) : ℝ := (Real.sqrt K.det)⁻¹

/-- **`brick-ball-floor`, half 2, in the form the producer consumes.**  If the ball of radius `r`
lies in `Ell K a`, then `r^(2d)·det K ≤ 1`; contrapositively, `Φ = 1/√(det K) ≥ r^d`: a body that
carries a ball of radius `r` cannot have volume potential below `r^d`. -/
theorem rpow_le_volPot {K : Matrix ι ι ℝ} {r : ℝ} (hr : 0 < r) (hK : K.PosDef)
    (hfloor : r ^ (2 * Fintype.card ι) * K.det ≤ 1) :
    r ^ Fintype.card ι ≤ volPot K := by
  have hd : 0 < Real.sqrt K.det := Real.sqrt_pos.2 hK.det_pos
  have hpos : 0 < r ^ Fintype.card ι := pow_pos hr _
  have hsq : (r ^ Fintype.card ι) ^ 2 = r ^ (2 * Fintype.card ι) := by
    rw [← pow_mul, Nat.mul_comm]
  have hx2 : (r ^ Fintype.card ι * Real.sqrt K.det) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hK.det_pos.le, hsq]
    exact hfloor
  have hx : 0 < r ^ Fintype.card ι * Real.sqrt K.det := mul_pos hpos hd
  have hmul : r ^ Fintype.card ι * Real.sqrt K.det ≤ 1 := by
    have h1 : (r ^ Fintype.card ι * Real.sqrt K.det - 1) *
        (r ^ Fintype.card ι * Real.sqrt K.det + 1) ≤ 0 := by nlinarith
    nlinarith
  have h1 : r ^ Fintype.card ι ≤ 1 / Real.sqrt K.det := by
    rw [le_div_iff₀ hd]
    exact hmul
  calc r ^ Fintype.card ι ≤ 1 / Real.sqrt K.det := h1
    _ = volPot K := by rw [volPot, div_eq_inv_mul, mul_one]

/-- **The composition recorded by `brick-ball-floor`.**  Half 1 says every point of the body with
positive margins carries a ball of radius `r` inside the body; half 2 (applied to that ball inside
the covering ellipsoid) bounds the determinant.  Composition gives the single determinant floor the
producer uses.  `hvol` is half 2 instantiated at the body. -/
theorem floor_of_ball {P : Set (ι → ℝ)} {K : Matrix ι ι ℝ} {r : ℝ}
    (hball : ∀ u, P u → eucBall u r ⊆ P)
    (hvol : ∀ u, eucBall u r ⊆ P → r ^ (2 * Fintype.card ι) * K.det ≤ 1) :
    ∀ u, P u → r ^ (2 * Fintype.card ι) * K.det ≤ 1 :=
  fun u hu => hvol u (hball u hu)

/-- **Empty body from a squeezed ellipsoid.**  If every body point forces `r^(2d)·det K ≤ 1`, but
the potential satisfies `Φ < r^d`, then the body has no point at all: this is the termination
condition of the producer, fed by the floor. -/
theorem empty_of_floor {P : Set (ι → ℝ)} {K : Matrix ι ι ℝ} {r : ℝ}
    (hr : 0 < r) (hK : K.PosDef)
    (hfloor : ∀ u, P u → r ^ (2 * Fintype.card ι) * K.det ≤ 1)
    (hsmall : volPot K < r ^ Fintype.card ι) :
    ∀ u, ¬ P u := by
  intro u hu
  have h1 := rpow_le_volPot hr hK (hfloor u hu)
  linarith

end Geometry

/-! ### Flattening the matrix body

The engine runs in the vector space of `n × n` real matrices, flattened to `Fin (n * n) → ℝ`.
`StrictBody` is the *strict* threshold body the refutation works on: unit-diagonal semidefinite
matrices with `tr (A Z) ≤ t - εr`.  Its complement is what `Answerε.refuted` asserts. -/

/-- The row-major flattening of a matrix, onto `Fin (n*n)` by `finProdFinEquiv`.

`Fin (n*n)` (rather than `Fin (n * n)`) is deliberate: it is the index type at which
`EngineIterates`/`EllipsoidStep` are stated, so `Ell` and `volPot` below are the compiled ones
*definitionally*, and `EngineIterates.body_containment`'s conclusion can be used as `Squeeze.cover`
without a change of variable. -/
def flat (X : Matrix (Fin n) (Fin n) ℝ) : Fin (n * n) → ℝ :=
  fun k => X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The strict threshold body at slack `εr`, as a set of flattened matrices. -/
def StrictBody (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) (εr : ℚ) : Set (Fin (n * n) → ℝ) :=
  {z | ∃ Z : Matrix (Fin n) (Fin n) ℝ,
    IsUnitDiagPSD Z ∧
      (A * Z).trace ≤ (t : ℝ) - (εr : ℝ) ∧ z = flat Z}

/-- **The refuted branch, delivered by geometry.**  Suppose the engine's final ellipsoid
`(K, a)` covers the strict body `{tr ≤ t - εr}` (`hcover`, `EngineIterates.body_containment`),
the ball floor holds on it (`hfloor`, `brick-ball-floor`), and the run terminated below the floor
radius (`hsmall`, `EngineIterates.engine_run` with `ε = r^d`).  Then there is no feasible matrix
with trace at most `t - εr`: the engine's refutation, with its slack, is *sound*. -/
theorem refute_of_squeezed {A : Matrix (Fin n) (Fin n) ℝ} {t : ℚ} {εr : ℚ}
    {K : Matrix (Fin (n * n)) (Fin (n * n)) ℝ} {a : Fin (n * n) → ℝ} {r : ℝ}
    (hr : 0 < r) (hK : K.PosDef)
    (hcover : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (A * Z).trace ≤ (t : ℝ) - (εr : ℝ) →
        Ell K a (flat Z))
    (hfloor : ∀ u, StrictBody A t εr u → r ^ (2 * (n * n)) * K.det ≤ 1)
    (hsmall : volPot K < r ^ (n * n)) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace := by
  intro Z hZ
  by_contra hcon
  have hlt : (A * Z).trace < (t : ℝ) - (εr : ℝ) := not_le.mp hcon
  have hmem : StrictBody A t εr (flat Z) := ⟨Z, hZ, le_of_lt hlt, rfl⟩
  have hfl := hfloor (flat Z) hmem
  have hle : r ^ (n * n) ≤ volPot K := by
    have h := rpow_le_volPot (ι := Fin (n * n)) hr hK (by simpa using hfl)
    simpa using h
  linarith

/-- **The squeeze package**: exactly the data `EngineIterates.engine_run` produces at its stopping
time, together with the floor on the body.  Every field is an *output* of an already compiled
brick; this structure is the interface at which they meet. -/
structure Squeeze (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) (εr : ℚ) where
  /-- the termination radius of the volume potential -/
  r : ℝ
  /-- it is positive -/
  r_pos : 0 < r
  /-- the final ellipsoid's shape matrix (a rational iterate, cast to `ℝ`) -/
  K : Matrix (Fin (n * n)) (Fin (n * n)) ℝ
  /-- the final ellipsoid's centre -/
  a : Fin (n * n) → ℝ
  /-- the iterate is positive definite (`EngineIterates.Aat_cast_posDef`) -/
  posDef : K.PosDef
  /-- the strict body is inside the final ellipsoid (`EngineIterates.body_containment`) -/
  cover : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
    IsUnitDiagPSD Z → (A * Z).trace ≤ (t : ℝ) - (εr : ℝ) →
      Ell K a (flat Z)
  /-- the ball floor on the strict body (`brick-ball-floor`) -/
  floor : ∀ u, StrictBody A t εr u → r ^ (2 * (n * n)) * K.det ≤ 1
  /-- the potential fell below the floor radius (`EngineIterates.engine_run`) -/
  small : volPot K < r ^ (n * n)

/-- **A squeeze refutes its threshold, with slack.** -/
theorem Squeeze.refute {A : Matrix (Fin n) (Fin n) ℝ} {t : ℚ} {εr : ℚ}
    (s : Squeeze A t εr) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (t : ℝ) - (εr : ℝ) ≤ (A * Z).trace :=
  refute_of_squeezed s.r_pos s.posDef s.cover s.floor s.small

/-- The strict body is inside the covering ellipsoid whenever every flattened feasible matrix is. -/
theorem strictBody_subset_ell {A : Matrix (Fin n) (Fin n) ℝ} {t : ℚ} {εr : ℚ}
    {K : Matrix (Fin (n * n)) (Fin (n * n)) ℝ} {a : Fin (n * n) → ℝ}
    (hcover : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (A * Z).trace ≤ (t : ℝ) - (εr : ℝ) →
        Ell K a (flat Z)) :
    ∀ z, StrictBody A t εr z → Ell K a z := by
  rintro z ⟨Z, hZ, htr, rfl⟩
  exact hcover Z hZ htr

/-- **`Squeeze` from the engine + the two halves of `brick-ball-floor`.**  This is the exact
division of labour between the two bricks:

* `hcover`  — `EngineIterates.body_containment` (the run's ellipsoid covers the strict body);
* `hball`   — `brick-ball-floor`, half 1: a body point carries a ball of radius `r` inside the body;
* `hvol`    — `brick-ball-floor`, half 2: a ball of radius `r` inside `Ell K a` forces
              `r^(2d)·det K ≤ 1` (the ellipsoid volume identity);
* `hsmall`  — `EngineIterates.engine_run`'s termination, `Φ_K < r^d`.

The composition is `floor_of_ball`: the two halves give the determinant floor on the whole body,
and `Squeeze` is then immediate. -/
noncomputable def squeeze_of_engine {A : Matrix (Fin n) (Fin n) ℝ} {t : ℚ} {εr : ℚ}
    {K : Matrix (Fin (n * n)) (Fin (n * n)) ℝ} {a : Fin (n * n) → ℝ} {r : ℝ}
    (hr : 0 < r) (hK : K.PosDef)
    (hcover : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (A * Z).trace ≤ (t : ℝ) - (εr : ℝ) →
        Ell K a (flat Z))
    (hball : ∀ u, StrictBody A t εr u → eucBall u r ⊆ StrictBody A t εr)
    (hvol : ∀ u, eucBall u r ⊆ Ell K a → r ^ (2 * (n * n)) * K.det ≤ 1)
    (hsmall : volPot K < r ^ (n * n)) : Squeeze A t εr where
  r := r
  r_pos := hr
  K := K
  a := a
  posDef := hK
  cover := hcover
  floor := by
    have hsub := strictBody_subset_ell hcover
    intro u hu
    exact hvol u (Set.Subset.trans (hball u hu) hsub)
  small := hsmall

/-- **A squeeze certifies that the strict body is empty** — the consistency check that the
interface cannot be met by a nonempty body.  (Note the two conclusions: `Squeeze.refute` gives the
driver's boundary-inclusive form `t - εr ≤ tr`; emptiness of the *set* `StrictBody` is the
stronger statement, and it is what the floor plus `Φ < r^d` proves directly.) -/
theorem Squeeze.body_empty {A : Matrix (Fin n) (Fin n) ℝ} {t : ℚ} {εr : ℚ}
    (s : Squeeze A t εr) : ∀ u, ¬ StrictBody A t εr u := by
  intro u hu
  have hfl : s.r ^ (2 * Fintype.card (Fin (n * n))) * s.K.det ≤ 1 := by
    simpa using s.floor u hu
  have hle : s.r ^ (n * n) ≤ volPot s.K := by
    have h := rpow_le_volPot (ι := Fin (n * n)) s.r_pos s.posDef hfl
    simpa using h
  linarith [s.small]

/-! ### The producer -/

/-- **The engine's outcome at one threshold**: a certified witness (rounding out), or a squeeze
(the ellipsoid run's termination, refuting the body with slack). -/
inductive Outcome (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) (εw εr : ℚ) : Type where
  /-- the run met a certified feasible point, up to the rounding slack `εw` -/
  | found (X : Matrix (Fin n) (Fin n) ℝ)
      (hX : IsUnitDiagPSD X)
      (htr : (A * X).trace ≤ (t : ℝ) + (εw : ℝ))
  /-- the run terminated below the ball floor, refuting the body down to `t - εr` -/
  | squeezed (s : Squeeze A t εr)

/-- **The producer**: whatever the engine's outcome, it *is* an `Answerε` at that threshold. -/
def Outcome.toAnswer {A : Matrix (Fin n) (Fin n) ℝ} {t : ℚ} {εw εr : ℚ} :
    Outcome A t εw εr → Answerε A t εw εr
  | .found X hX htr => .witness X hX htr
  | .squeezed s => .refuted s.refute

/-- A producer is a total map from rational thresholds to engine outcomes.  `ThresholdDriver`'s
contract `∀ t, Answer A t` is the case `εw = εr = 0` of `∀ t, Answerε A t εw εr`. -/
abbrev Producer (A : Matrix (Fin n) (Fin n) ℝ) (εw εr : ℚ) : Type :=
  ∀ t : ℚ, Outcome A t εw εr

/-- **The producer's correctness theorem**: a total producer answers every rational threshold. -/
def Producer.answers {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (p : Producer A εw εr) : ∀ t : ℚ, Answerε A t εw εr :=
  fun t => (p t).toAnswer

/-- The exact per-threshold engine of `ThresholdDriver` is a zero-slack producer. -/
def Producer.ofExact {A : Matrix (Fin n) (Fin n) ℝ}
    (p : ∀ t : ℚ, Answer A t) : ∀ t : ℚ, Answerε A t 0 0 :=
  fun t => (p t).toSlack

/-- The producer's contract is inhabited: the zero matrix is answered exactly at every rational
threshold (identity on the feasible side, the trivial refutation on the other) — the same witness
as `ThresholdDriver.answer_zero`, at zero slack. -/
def producer_zero (t : ℚ) :
    Answerε (0 : Matrix (Fin n) (Fin n) ℝ) t 0 0 := by
  by_cases h : (0 : ℚ) ≤ t
  · refine Answerε.witness (1 : Matrix (Fin n) (Fin n) ℝ) ⟨Matrix.PosSemidef.one, ?_⟩ ?_
    · intro i; simp
    · have hcast : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
      simpa using hcast
  · refine Answerε.refuted fun Z _ => ?_
    have hcast : (t : ℝ) ≤ 0 := by
      have h' : t ≤ 0 := le_of_not_ge h
      exact_mod_cast h'
    simpa using hcast

/-! ## 3.  The slack bisection: thirteen calls at any precision

This is `ThresholdDriver`'s outer layer re-run on `Answerε`.  The only changes are the two slack
terms in the bracket invariants; the halving argument, the starting bracket and the sandwich are
the same, and at `εw = εr = 0` the statements are `ThresholdDriver`'s verbatim. -/

/-- The bracket with slack: `lo` is refuted down to `lo - εr`, `hi` is witnessed up to `hi + εw`. -/
structure SlackBrack (A : Matrix (Fin n) (Fin n) ℝ) (εw εr : ℚ) where
  /-- refuted threshold (with slack `εr`) -/
  lo : ℚ
  /-- witnessed threshold (with slack `εw`) -/
  hi : ℚ
  /-- the bracket is ordered -/
  lo_le_hi : lo ≤ hi
  /-- the witness carried forward from the last `witness` answer -/
  wit : Matrix (Fin n) (Fin n) ℝ
  /-- it is feasible -/
  wit_feas : IsUnitDiagPSD wit
  /-- and its trace is at most `hi + εw` -/
  wit_tr : (A * wit).trace ≤ (hi : ℝ) + (εw : ℝ)
  /-- the refutation at the low endpoint, down to `lo - εr` -/
  lo_sound : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
    IsUnitDiagPSD Z → (lo : ℝ) - (εr : ℝ) ≤ (A * Z).trace

/-- **One slack bisection step**: query the midpoint and move the matching endpoint. -/
noncomputable def step {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr) : SlackBrack A εw εr :=
  match eng ((B.lo + B.hi) / 2) with
  | .witness X hX htr =>
      { lo := B.lo
        hi := (B.lo + B.hi) / 2
        lo_le_hi := by linarith [B.lo_le_hi]
        wit := X
        wit_feas := hX
        wit_tr := htr
        lo_sound := B.lo_sound }
  | .refuted hlb =>
      { lo := (B.lo + B.hi) / 2
        hi := B.hi
        lo_le_hi := by linarith [B.lo_le_hi]
        wit := B.wit
        wit_feas := B.wit_feas
        wit_tr := B.wit_tr
        lo_sound := hlb }

/-- Each step halves the bracket width. -/
theorem step_width {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr) :
    (step eng B).hi - (step eng B).lo = (B.hi - B.lo) / 2 := by
  unfold step
  split <;> ring

/-- `k` slack bisection steps, each one engine call. -/
noncomputable def iter {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr) : ℕ → SlackBrack A εw εr
  | 0 => B
  | (k + 1) => step eng (iter eng B k)

/-- After `k` steps the bracket width is `(hi₀ − lo₀)/2^k`. -/
theorem iter_width {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr) :
    ∀ k : ℕ, (iter eng B k).hi - (iter eng B k).lo = (B.hi - B.lo) / 2 ^ k
  | 0 => by simp [iter]
  | (k + 1) => by
      have hrec : (iter eng B (k + 1)).hi - (iter eng B (k + 1)).lo
          = ((iter eng B k).hi - (iter eng B k).lo) / 2 := by
        simp only [iter]
        exact step_width eng (iter eng B k)
      rw [hrec, iter_width eng B k, div_div, pow_succ]

/-- A step never raises the witnessed endpoint. -/
theorem step_hi_le {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr) :
    (step eng B).hi ≤ B.hi := by
  unfold step
  split
  · linarith [B.lo_le_hi]
  · exact le_rfl

/-- The witnessed endpoint never rises above where it started. -/
theorem hi_le_start {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr) :
    ∀ k : ℕ, (iter eng B k).hi ≤ B.hi
  | 0 => by simp [iter]
  | (k + 1) => by
      have h1 : (iter eng B (k + 1)).hi ≤ (iter eng B k).hi := by
        simp only [iter]
        exact step_hi_le eng (iter eng B k)
      exact h1.trans (hi_le_start eng B k)

/-- The witnessed endpoint gives a **lower** bound for the SDP value, degraded by `εw/4`. -/
theorem lower_bound {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ} {εw εr : ℚ}
    (hS : IsMaxcutSDPValue A S) (B : SlackBrack A εw εr) :
    (V A - (B.hi : ℝ) - (εw : ℝ)) / 4 ≤ S := by
  have hobj : maxcutRelaxationObjective A B.wit
      = (V A - (A * B.wit).trace) / 4 :=
    maxcut_objective_eq A B.wit (transpose_eq_of_posSemidef B.wit_feas.1)
  have hle : maxcutRelaxationObjective A B.wit ≤ S :=
    hS.1 ⟨B.wit, B.wit_feas, rfl⟩
  rw [hobj] at hle
  linarith [B.wit_tr]

/-- The refuted endpoint gives an **upper** bound for the SDP value, degraded by `εr/4`. -/
theorem upper_bound {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ} {εw εr : ℚ}
    (hS : IsMaxcutSDPValue A S) (B : SlackBrack A εw εr) :
    S ≤ (V A - (B.lo : ℝ)) / 4 + (εr : ℝ) / 4 := by
  refine hS.2 (Set.forall_mem_image.mpr fun Z hZ => ?_)
  rw [maxcut_objective_eq A Z (transpose_eq_of_posSemidef hZ.1)]
  have h := B.lo_sound Z hZ
  have hV : V A = ∑ i, ∑ j, A i j := rfl
  rw [hV]
  linarith

/-- **The slack driver, abstractly**: after `k` steps the SDP value is trapped between the two
endpoints, up to `(εw + εr)/4`. -/
theorem driver_bounds {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ} {εw εr : ℚ}
    (hS : IsMaxcutSDPValue A S)
    (eng : ∀ t : ℚ, Answerε A t εw εr) (B₀ : SlackBrack A εw εr) (k : ℕ) :
    (V A - ((iter eng B₀ k).hi : ℝ) - (εw : ℝ)) / 4 ≤ S ∧
      S ≤ (V A - ((iter eng B₀ k).lo : ℝ)) / 4 + (εr : ℝ) / 4 :=
  ⟨lower_bound hS (iter eng B₀ k), upper_bound hS (iter eng B₀ k)⟩

/-! ### The starting bracket (entrywise nonnegative, zero diagonal) -/

theorem isUnitDiagPSD_one : IsUnitDiagPSD (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨Matrix.PosSemidef.one, fun i => by simp⟩

/-- Entries of a unit-diagonal semidefinite matrix are at most `1`. -/
theorem apply_le_one {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) (i j : Fin n) : X i j ≤ 1 := by
  classical
  have hM : (X.submatrix ![i, j] ![i, j]).PosSemidef := hX.submatrix _
  have hv := hM.dotProduct_mulVec_nonneg (fun k : Fin 2 => if k = 0 then (1 : ℝ) else -1)
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Fin.sum_univ_two,
    star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, hdiag] at hv
  norm_num at hv
  have hsym : X j i = X i j := by
    simpa using (Matrix.IsHermitian.apply hX.1 i j)
  rw [hsym] at hv
  linarith

/-- Entries of a unit-diagonal semidefinite matrix are at least `-1`. -/
theorem neg_one_le_apply {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) (i j : Fin n) : -1 ≤ X i j := by
  classical
  have hM : (X.submatrix ![i, j] ![i, j]).PosSemidef := hX.submatrix _
  have hv := hM.dotProduct_mulVec_nonneg (fun k : Fin 2 => (1 : ℝ))
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Fin.sum_univ_two,
    star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, hdiag] at hv
  norm_num at hv
  have hsym : X j i = X i j := by
    simpa using (Matrix.IsHermitian.apply hX.1 i j)
  rw [hsym] at hv
  linarith

/-- Entries of a unit-diagonal semidefinite matrix lie in `[-1,1]`. -/
theorem abs_apply_le_one {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsUnitDiagPSD X) (i j : Fin n) : |X i j| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_apply hX.1 hX.2 i j, apply_le_one hX.1 hX.2 i j⟩

/-- **The trace is bounded below by minus the `ℓ¹` mass of `A`** on the feasible set: the only
estimate the refuted side of the driver needs, and the source of the starting bracket. -/
theorem neg_abs_sum_le_trace (A Z : Matrix (Fin n) (Fin n) ℝ)
    (hZ : IsUnitDiagPSD Z) :
    -(∑ i, ∑ j, |A i j|) ≤ (A * Z).trace := by
  have hsym : ∀ i j : Fin n, Z j i = Z i j := by
    intro i j
    have h := transpose_eq_of_posSemidef hZ.1
    have h2 := congrFun (congrFun h j) i
    simpa [Matrix.transpose_apply] using h2.symm
  have htrace : (A * Z).trace = ∑ i, ∑ j, A i j * Z i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym]
  have hterm : ∀ (i j : Fin n), 0 ≤ A i j * Z i j + |A i j| := by
    intro i j
    have hz : |Z i j| ≤ 1 := abs_apply_le_one hZ i j
    have h1 : -(|A i j| * |Z i j|) ≤ A i j * Z i j := by
      have h := neg_abs_le (A i j * Z i j)
      rwa [abs_mul] at h
    have h2 : |A i j| * |Z i j| ≤ |A i j| := by
      calc |A i j| * |Z i j| ≤ |A i j| * 1 :=
            mul_le_mul_of_nonneg_left hz (abs_nonneg _)
        _ = |A i j| := mul_one _
    linarith
  rw [htrace]
  have hnonneg : (0 : ℝ) ≤ ∑ i, ∑ j, (A i j * Z i j + |A i j|) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j
  have hsplit : (∑ i, ∑ j, (A i j * Z i j + |A i j|))
      = (∑ i, ∑ j, A i j * Z i j) + (∑ i, ∑ j, |A i j|) := by
    simp only [Finset.sum_add_distrib]
  linarith

/-- The trace of `A` against the identity is the diagonal sum. -/
theorem trace_mul_one (A : Matrix (Fin n) (Fin n) ℝ) : (A * 1).trace = ∑ i, A i i := by
  simp [Matrix.trace]

/-- **The slack start bracket**: `lo = -R` is refuted (down to `-R - εr`), `hi = 0` is witnessed by
the identity, whose trace is the diagonal sum `0`. -/
noncomputable def startBrack {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (hεw0 : 0 ≤ εw) (hεr0 : 0 ≤ εr)
    (_hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0) (R : ℚ)
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ)) : SlackBrack A εw εr where
  lo := -R
  hi := 0
  lo_le_hi := by
    have h0 : (0 : ℝ) ≤ (R : ℝ) := by
      rw [← hRabs]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    have h0q : (0 : ℚ) ≤ R := by exact_mod_cast h0
    linarith
  wit := 1
  wit_feas := isUnitDiagPSD_one
  wit_tr := by
    rw [trace_mul_one]
    have hzero : (∑ i, A i i) = 0 := Finset.sum_eq_zero fun i _ => hAz i
    rw [hzero]
    have hε : (0 : ℝ) ≤ (εw : ℝ) := by exact_mod_cast hεw0
    simpa using hε
  lo_sound := by
    intro Z hZ
    have h := neg_abs_sum_le_trace A Z hZ
    have hcast : ((-R : ℚ) : ℝ) = -(R : ℝ) := by push_cast; ring
    have hε : (0 : ℝ) ≤ (εr : ℝ) := by exact_mod_cast hεr0
    rw [hcast, ← hRabs]
    linarith

/-- The start bracket's width is the total weight. -/
theorem startBrack_width {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}
    (hεw0 : 0 ≤ εw) (hεr0 : 0 ≤ εr)
    (hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0) (R : ℚ)
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ)) :
    (startBrack hεw0 hεr0 hAn hAz R hRabs).hi
      - (startBrack hεw0 hεr0 hAn hAz R hRabs).lo = R := by
  simp [startBrack]

/-! ### A dual certificate fills the refuted constructor

The rounding factory emits a dual-feasible `y` (`hy : diagonal y + A ⪰ 0`); it refutes every
threshold below `-∑ᵢ yᵢ`.  This is the second, certificate-based route to `.refuted` — it does not
need the ellipsoid at all, and it shows the constructor is inhabited on concrete data. -/

theorem dual_refutes {A : Matrix (Fin n) (Fin n) ℝ} {y : Fin n → ℝ} {t : ℚ}
    (hy : (Matrix.diagonal y + A).PosSemidef) (hyt : (t : ℝ) ≤ -(∑ i, y i)) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      IsUnitDiagPSD Z → (t : ℝ) ≤ (A * Z).trace := by
  intro Z hZ
  have h0 : 0 ≤ ((Matrix.diagonal y + A) * Z).trace :=
    psd_trace_mul_nonneg hy hZ.1
  rw [Matrix.add_mul, Matrix.trace_add, trace_diagonal_mul_of_unitDiag y hZ.2] at h0
  linarith

/-- The dual certificate of a display pair, as an exact refuted answer. -/
def answer_of_dual {A : Matrix (Fin n) (Fin n) ℝ} {y : Fin n → ℝ} {t : ℚ}
    (hy : (Matrix.diagonal y + A).PosSemidef) (hyt : (t : ℝ) ≤ -(∑ i, y i)) :
    Answer A t :=
  Answer.infeasible (dual_refutes hy hyt)

/-- **The leaf's value from a slack engine, abstractly.**  For entrywise nonnegative data with
zero diagonal and rational total weight `R = V A`, thirteen bisection steps give a rational `Lq`
with

    0 ≤ Lq,   Lq ≤ S,   S − Lq ≤ R/32768 + (εw + εr)/4.

`R/32768` is `(hi − lo)/4` after thirteen halvings of the starting width `R`; the two slack terms
are the price of not being able to decide feasibility exactly.  At `εw = εr = 0` this is
`ThresholdDriver.leafB_threshold_driver`. -/
theorem leafB_threshold_driver_slack {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : IsMaxcutSDPValue A S)
    (hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0)
    (R : ℚ) (hR : V A = (R : ℝ))
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ))
    {εw εr : ℚ} (hεw0 : 0 ≤ εw) (hεr0 : 0 ≤ εr) (hεwR : εw ≤ R)
    (eng : ∀ t : ℚ, Answerε A t εw εr) :
    ∃ Lq : ℚ, 0 ≤ Lq ∧ (Lq : ℝ) ≤ S ∧
      S - (Lq : ℝ) ≤ (R : ℝ) / 32768 + ((εw : ℝ) + (εr : ℝ)) / 4 := by
  -- the starting bracket and thirteen steps of the bisection
  set B₀ : SlackBrack A εw εr := startBrack hεw0 hεr0 hAn hAz R hRabs with hB₀
  set Bk : SlackBrack A εw εr := iter eng B₀ 13 with hBk
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by
    rw [← hRabs]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hR0q : (0 : ℚ) ≤ R := by exact_mod_cast hR0
  -- the bracket has halved thirteen times: width `R/2^13`
  have hwQ : Bk.hi - Bk.lo = R / 2 ^ 13 := by
    rw [hBk, iter_width, startBrack_width]
  have hwR : (Bk.hi : ℝ) - (Bk.lo : ℝ) = (R : ℝ) / 2 ^ 13 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hwQ
    push_cast at h
    simpa using h
  -- the witnessed endpoint never rose above `0`
  have hhi : Bk.hi ≤ 0 := by
    have h := hi_le_start eng B₀ 13
    rw [← hBk] at h
    have h0 : B₀.hi = 0 := rfl
    linarith
  -- the two sides of the slack sandwich at the final bracket
  have hlow : (V A - (Bk.hi : ℝ) - (εw : ℝ)) / 4 ≤ S :=
    (driver_bounds hS eng B₀ 13).1
  have hup : S ≤ (V A - (Bk.lo : ℝ)) / 4 + (εr : ℝ) / 4 :=
    (driver_bounds hS eng B₀ 13).2
  refine ⟨(R - Bk.hi - εw) / 4, ?_, ?_, ?_⟩
  · -- nonnegative
    have h1 : Bk.hi + εw ≤ R := by linarith
    linarith
  · -- below the SDP value
    have hcast : (((R - Bk.hi - εw) / 4 : ℚ) : ℝ)
        = ((R : ℝ) - (Bk.hi : ℝ) - (εw : ℝ)) / 4 := by push_cast; ring
    rw [hcast, ← hR]
    exact hlow
  · -- and the gap is at most `R/32768 + (εw + εr)/4`
    have hcast : (((R - Bk.hi - εw) / 4 : ℚ) : ℝ)
        = ((R : ℝ) - (Bk.hi : ℝ) - (εw : ℝ)) / 4 := by push_cast; ring
    rw [hcast, ← hR]
    have hstep : (R : ℝ) / 2 ^ 13 / 4 = (R : ℝ) / 32768 := by
      rw [div_div]
      norm_num
    nlinarith [hup, hwR]

/-! ## 4.  Leaf B at slack: thirteen calls, and the precision budget they imply -/

/-- **The leaf's bound with a precision budget.**  With the same thirteen-call driver, if the two
slacks of the producer satisfy `εw + εr ≤ R/15000` then the sharp bound `R/32768 + (εw+εr)/4` is at
most `R/20000`, i.e. exactly `ThresholdDriver`'s bound despite the engine being unable to decide
feasibility exactly.  (`R = V A` is the rational total weight; for a weighted graph `G`,
`R = 2 ∑ₑ wₑ` and the statement is `εw + εr ≤ W/7500 ⟹ S − L ≤ W/10000`, see
`Check_answer_producer_wMatrix.lean`.) -/
theorem leafB_threshold_driver_budget {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : IsMaxcutSDPValue A S)
    (hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0)
    (R : ℚ) (hR : V A = (R : ℝ))
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ))
    {εw εr : ℚ} (hεw0 : 0 ≤ εw) (hεr0 : 0 ≤ εr) (hεwR : εw ≤ R)
    (hbudget : (εw : ℝ) + (εr : ℝ) ≤ (R : ℝ) / 15000)
    (eng : ∀ t : ℚ, Answerε A t εw εr) :
    ∃ Lq : ℚ, 0 ≤ Lq ∧ (Lq : ℝ) ≤ S ∧ S - (Lq : ℝ) ≤ (R : ℝ) / 20000 := by
  obtain ⟨Lq, h0, h1, h2⟩ :=
    leafB_threshold_driver_slack hS hAn hAz R hR hRabs hεw0 hεr0 hεwR eng
  refine ⟨Lq, h0, h1, ?_⟩
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by
    rw [← hRabs]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hquarter : ((εw : ℝ) + (εr : ℝ)) / 4 ≤ (R : ℝ) / 60000 := by linarith
  have hkey : (R : ℝ) / 32768 + (R : ℝ) / 60000 ≤ (R : ℝ) / 20000 := by
    have h1 : (R : ℝ) / 32768 + (R : ℝ) / 60000 = (R : ℝ) * (1 / 32768 + 1 / 60000) := by ring
    have h2 : (R : ℝ) / 20000 = (R : ℝ) * (1 / 20000) := by ring
    rw [h1, h2]
    refine mul_le_mul_of_nonneg_left ?_ hR0
    norm_num
  linarith

/-- **The exact driver is the zero-slack case.**  With `εw = εr = 0` the slack theorem gives back
`ThresholdDriver.leafB_threshold_driver` verbatim: a total exact per-threshold engine
(`∀ t, Answer A t`) suffices.  So the slack contract is a strict generalisation of the compiled
one, and the compiled leaf theorem is a corollary of this file. -/
theorem leafB_threshold_driver_exact {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : IsMaxcutSDPValue A S)
    (hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0)
    (R : ℚ) (hR : V A = (R : ℝ))
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ))
    (eng : ∀ t : ℚ, Answer A t) :
    ∃ Lq : ℚ, 0 ≤ Lq ∧ (Lq : ℝ) ≤ S ∧ S - (Lq : ℝ) ≤ (R : ℝ) / 20000 := by
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by
    rw [← hRabs]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hR0q : (0 : ℚ) ≤ R := by exact_mod_cast hR0
  have hbudget : ((0 : ℚ) : ℝ) + ((0 : ℚ) : ℝ) ≤ (R : ℝ) / 15000 := by
    have hzero : ((0 : ℚ) : ℝ) + ((0 : ℚ) : ℝ) = 0 := by norm_num
    rw [hzero]
    exact div_nonneg hR0 (by norm_num)
  exact leafB_threshold_driver_budget hS hAn hAz R hR hRabs le_rfl le_rfl hR0q hbudget
    (Producer.ofExact eng)

/-- **The precision budget in the form the engine bricks meet it.**  For a weight matrix whose
total weight is `W` (`V A = 2W`), the two slacks may take up to `W/7500` between them:
`εw + εr ≤ W/7500 ⟹ S − L ≤ W/10000`. -/
theorem leafB_budget_of_weight {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : IsMaxcutSDPValue A S)
    (hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0)
    (R : ℚ) (W : ℝ) (hW : 0 ≤ W) (hV : V A = (R : ℝ)) (hRV : (R : ℝ) = 2 * W)
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ))
    {εw εr : ℚ} (hεw0 : 0 ≤ εw) (hεr0 : 0 ≤ εr) (hεwR : εw ≤ R)
    (hbudget : (εw : ℝ) + (εr : ℝ) ≤ W / 7500)
    (eng : ∀ t : ℚ, Answerε A t εw εr) :
    ∃ Lq : ℚ, 0 ≤ Lq ∧ (Lq : ℝ) ≤ S ∧ S - (Lq : ℝ) ≤ W / 10000 := by
  have hbud' : (εw : ℝ) + (εr : ℝ) ≤ (R : ℝ) / 15000 := by
    have h : (R : ℝ) / 15000 = W / 7500 := by rw [hRV]; ring
    linarith
  obtain ⟨Lq, h0, h1, h2⟩ :=
    leafB_threshold_driver_budget hS hAn hAz R hV hRabs hεw0 hεr0 hεwR hbud' eng
  refine ⟨Lq, h0, h1, ?_⟩
  have hW' : (R : ℝ) / 20000 = W / 10000 := by rw [hRV]; ring
  linarith

/-! ## 5.  Axioms -/

#print axioms QMCLeafB.AnswerProducer.Producer.answers
#print axioms QMCLeafB.AnswerProducer.producer_zero
#print axioms QMCLeafB.AnswerProducer.squeeze_of_engine
#print axioms QMCLeafB.AnswerProducer.Squeeze.body_empty
#print axioms QMCLeafB.AnswerProducer.dual_refutes
#print axioms QMCLeafB.AnswerProducer.Answer.toSlack
#print axioms QMCLeafB.AnswerProducer.Answerε.toExact


