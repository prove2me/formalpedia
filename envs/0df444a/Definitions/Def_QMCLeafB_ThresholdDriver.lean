-- Prove2me | Definitions.Def_QMCLeafB_ThresholdDriver
-- name    : QMCLeafB_ThresholdDriver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:09:29.282458+00:00
-- url     : https://prove2.me/theorems/744fcfe3-a795-4c8b-b4d6-fc89360a40f5
-- title:
--   QMCLeafB ThresholdDriver
-- statement:
--   # brick-threshold-driver — the outer threshold search of leaf B
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_Core
/-
# brick-threshold-driver — the outer threshold search of leaf B

Leaf B's lower value `L : Input → ℚ≥0` has to satisfy, per graph `G`, with
`S := sdpValue (QMCLeafB.wMatrix G)`,

    L G ≤ S   and   S − L G ≤ W/10000 .

Every *inner* brick of phase 3 answers a question about a **fixed rational threshold** `t`:
the ellipsoid engine, run on the threshold body

    K(t) = {X | X unit-diagonal ⪰ 0,  tr(A X) ≤ t},

either produces a feasible witness `X` with `tr(A X) ≤ t`, or proves the body empty.  This file
is the missing **outer** layer: it turns those fixed-threshold answers into `L`, and it is the
only place where the number of engine calls is decided.

## The two answers, and why they are the right ones

For a rational `t` let `V A = ∑ᵢ ∑ⱼ Aᵢⱼ` and `obj A X = (V A − tr(A X))/4`, so
`S = sdpValue A` is the least upper bound of `obj A ·` over the unit-diagonal PSD matrices
(`QMCLeafB.maxcut_objective_eq`).  Then

* a witness `X` with `tr(A X) ≤ t` gives `(V A − t)/4 ≤ obj A X ≤ S` — a **lower** bound;
* emptiness of `K(t)`, i.e. `t ≤ tr(A Z)` for every feasible `Z`, gives `S ≤ (V A − t)/4` —
  an **upper** bound.

So each answer is a rational threshold sandwiching `S` from one side, and bisection on `t`
halves the remaining width.  Note the branch does not need a duality theorem: for *every* `t`
at least one of the two statements holds (below the minimum both do), so the contract
`∀ t, Answer A t` is satisfiable by construction and is exactly what a correct ellipsoid engine
can be asked to deliver.

## Result: thirteen engine calls, uniformly in `n` and in the weights

`Brack A` is the driver's state: a rational `lo` proved below every feasible trace, a rational
`hi` carrying a witness, and `lo ≤ hi`.  `step` halves `hi − lo`, so `iter eng B₀ k` has
`hi − lo = (hi₀ − lo₀)/2^k`.  With the concrete start `lo₀ = −∑ᵢ ∑ⱼ Aᵢⱼ`, `hi₀ = 0` (witness:
the identity matrix, whose trace is the diagonal sum) the starting width is exactly `V A`, so

    k = 13   ⟹   S − L ≤ V/32768 ≤ V/20000 = W/10000,

with **no** dependence on `n` or on the weights: the leaf's `L` is thirteen engine calls, each
inside the polynomial runtime budget the floor-adapter brick accounts for.

## Index

| statement | what it says |
|---|---|
| `Answer` | the engine's per-threshold answer: `feasible` witness or `infeasible` proof |
| `Answer.feasible_mono`, `Answer.infeasible_anti` | the two branches are monotone in `t` |
| `Brack` | the driver state and its two soundness invariants |
| `step`, `step_width` | one bisection step; the width halves |
| `lower_bound`, `upper_bound` | the two sides of the sandwich from a `Brack` |
| `iter`, `iter_width`, `driver_bounds` | `k` steps; width `(hi₀−lo₀)/2^k`; both bounds survive |
| `hl_le_start` | the witnessed endpoint never rises above its start |
| `startBrack` | the concrete start bracket for nonnegative zero-diagonal data |
| `leafB_threshold_driver` | the leaf's `∃ L, 0 ≤ L ∧ L ≤ S ∧ S − L ≤ V/20000` |
| `leafB_threshold_driver_wMatrix` | the same at `A = wMatrix G`, bound `W/10000` |
| `dual_refutes`, `answer_of_dual` | a display pair's dual certificate fills `Answer.infeasible` |
| `answer_of_primal` | an explicit feasible point fills `Answer.feasible` |
| `answer_zero` | the contract `∀ t, Answer A t` is inhabited at every threshold |
| `answer_of_range`, `leafB_threshold_driver_range` | the engine only has to answer `t ∈ [−R, 0]`; the leaf's bound from such an engine |
| `edgeA_trace`, `posSemidef_edgeW`, `edgeA_refute`, `edgeA_feasible`, `edgeA_answers` | the single-edge instance: both branches inhabited, meeting exactly at `t = −2` |

Compiles with `lake env lean` (Mathlib + the merged `Solutions/MergeAll3_m8`); no `sorry`, and
the only imports are the merged library's own.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.ThresholdDriver

variable {n : ℕ}

/-! ## 1.  Box and trace facts for unit-diagonal semidefinite matrices -/

/-- The identity matrix is unit-diagonal semidefinite. -/
theorem isUnitDiagPSD_one :
    ModernConvex.Relaxations.IsUnitDiagPSD (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨Matrix.PosSemidef.one, fun i => by simp⟩

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

/-- Entries of a unit-diagonal semidefinite matrix lie in `[-1, 1]`. -/
theorem abs_apply_le_one {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) (i j : Fin n) : |X i j| ≤ 1 := by
  rw [abs_le]
  exact ⟨neg_one_le_apply hX.1 hX.2 i j, apply_le_one hX.1 hX.2 i j⟩

/-- **The trace of `A Z` is bounded below by minus the `ℓ¹` mass of `A`**, because every entry
of a unit-diagonal semidefinite `Z` is in `[-1,1]`.  This is the only estimate the infeasibility
side of the driver needs: it supplies the *starting* lower threshold. -/
theorem neg_abs_sum_le_trace (A Z : Matrix (Fin n) (Fin n) ℝ)
    (hZ : ModernConvex.Relaxations.IsUnitDiagPSD Z) :
    -(∑ i, ∑ j, |A i j|) ≤ (A * Z).trace := by
  have hsym : ∀ i j : Fin n, Z j i = Z i j := by
    intro i j
    have h := QMCLeafB.transpose_eq_of_posSemidef hZ.1
    have := congrFun (congrFun h j) i
    simpa [Matrix.transpose_apply] using this.symm
  have htrace : (A * Z).trace = ∑ i, ∑ j, A i j * Z i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym]
  have hterm : ∀ i j : Fin n, 0 ≤ A i j * Z i j + |A i j| := by
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
theorem trace_mul_one (A : Matrix (Fin n) (Fin n) ℝ) :
    (A * 1).trace = ∑ i, A i i := by
  simp [Matrix.trace]

/-! ## 2.  The engine's answer at a fixed threshold -/

/-- **What the ellipsoid engine delivers at a fixed rational threshold `t`.**

* `feasible X`: `X` is a genuine unit-diagonal semidefinite point with `tr(A X) ≤ t`;
* `infeasible`: the *proof* that the threshold body is empty, i.e. that every unit-diagonal
  semidefinite `Z` has `t ≤ tr(A Z)`.

The proofs are carried with the data on purpose: the driver never has to re-establish them, so
the whole outer layer is a rational computation driven by a two-way branch. -/
inductive Answer (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) : Type where
  | feasible (X : Matrix (Fin n) (Fin n) ℝ)
      (hX : ModernConvex.Relaxations.IsUnitDiagPSD X)
      (htr : (A * X).trace ≤ (t : ℝ))
  | infeasible (hlb : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD Z → (t : ℝ) ≤ (A * Z).trace)

/-- A feasible witness at a threshold is still a feasible witness at every larger threshold. -/
theorem witness_mono {A : Matrix (Fin n) (Fin n) ℝ} {t t' : ℚ} (htt : t ≤ t')
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) (htr : (A * X).trace ≤ (t : ℝ)) :
    ∃ Y : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD Y ∧ (A * Y).trace ≤ (t' : ℝ) :=
  ⟨X, hX, htr.trans (by exact_mod_cast htt)⟩

/-- A refutation at a threshold is still a refutation at every smaller threshold. -/
theorem refute_mono {A : Matrix (Fin n) (Fin n) ℝ} {t t' : ℚ} (htt : t' ≤ t)
    (h : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD Z → (t : ℝ) ≤ (A * Z).trace) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD Z → (t' : ℝ) ≤ (A * Z).trace := by
  intro Z hZ
  have hcast : (t' : ℝ) ≤ (t : ℝ) := by exact_mod_cast htt
  exact hcast.trans (h Z hZ)

/-! ## 3.  The driver's state and one bisection step -/

/-- **The bracket.**  `hi` is a threshold we have *witnessed* (`tr A X ≤ hi` for some feasible
`X`), `lo` is a threshold we have *refuted* (`lo ≤ tr A Z` for all feasible `Z`), and
`lo ≤ hi`.  The two `Brack` fields `wit_tr` and `lo_sound` are exactly the two hypotheses of the
sandwich in `leafB_threshold_driver`. -/
structure Brack (A : Matrix (Fin n) (Fin n) ℝ) where
  /-- refuted threshold: below every feasible trace -/
  lo : ℚ
  /-- witnessed threshold: above some feasible trace -/
  hi : ℚ
  /-- the bracket is ordered -/
  lo_le_hi : lo ≤ hi
  /-- the witness carried forward from the last `feasible` answer -/
  wit : Matrix (Fin n) (Fin n) ℝ
  /-- it is feasible -/
  wit_feas : ModernConvex.Relaxations.IsUnitDiagPSD wit
  /-- and its trace is at most the witnessed endpoint -/
  wit_tr : (A * wit).trace ≤ (hi : ℝ)
  /-- the refutation at the low endpoint -/
  lo_sound : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
    ModernConvex.Relaxations.IsUnitDiagPSD Z → (lo : ℝ) ≤ (A * Z).trace

/-- **One bisection step**: query the midpoint and move the matching endpoint.  A `feasible`
answer raises `lo` to the midpoint's *counterpart*, `hi` drops to the midpoint; an `infeasible`
answer raises `lo` to the midpoint.  Either way the bracket stays ordered and the two soundness
invariants are preserved — that is the whole correctness of the outer layer. -/
noncomputable def step {A : Matrix (Fin n) (Fin n) ℝ}
    (eng : ∀ t : ℚ, Answer A t) (B : Brack A) : Brack A :=
  match h : eng ((B.lo + B.hi) / 2) with
  | .feasible X hX htr =>
      { lo := B.lo
        hi := (B.lo + B.hi) / 2
        lo_le_hi := by
          have h1 : B.lo ≤ (B.lo + B.hi) / 2 := by linarith [B.lo_le_hi]
          exact h1
        wit := X
        wit_feas := hX
        wit_tr := htr
        lo_sound := B.lo_sound }
  | .infeasible hlb =>
      { lo := (B.lo + B.hi) / 2
        hi := B.hi
        lo_le_hi := by linarith [B.lo_le_hi]
        wit := B.wit
        wit_feas := B.wit_feas
        wit_tr := B.wit_tr
        lo_sound := hlb }

/-- Each step halves the bracket width. -/
theorem step_width {A : Matrix (Fin n) (Fin n) ℝ}
    (eng : ∀ t : ℚ, Answer A t) (B : Brack A) :
    (step eng B).hi - (step eng B).lo = (B.hi - B.lo) / 2 := by
  unfold step
  split <;> ring

/-! ## 4.  The two sides of the sandwich from a bracket -/

/-- The witnessed endpoint gives a **lower** bound for the SDP value. -/
theorem lower_bound {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S) (B : Brack A) :
    (QMCLeafB.V A - (B.hi : ℝ)) / 4 ≤ S := by
  have hobj : ModernConvex.Relaxations.maxcutRelaxationObjective A B.wit
      = (QMCLeafB.V A - (A * B.wit).trace) / 4 :=
    QMCLeafB.maxcut_objective_eq A B.wit
      (QMCLeafB.transpose_eq_of_posSemidef B.wit_feas.1)
  have hle : ModernConvex.Relaxations.maxcutRelaxationObjective A B.wit ≤ S :=
    hS.1 ⟨B.wit, B.wit_feas, rfl⟩
  have htr : (A * B.wit).trace ≤ (B.hi : ℝ) := B.wit_tr
  rw [hobj] at hle
  linarith

/-- The refuted endpoint gives an **upper** bound for the SDP value. -/
theorem upper_bound {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S) (B : Brack A) :
    S ≤ (QMCLeafB.V A - (B.lo : ℝ)) / 4 := by
  refine hS.2 (Set.forall_mem_image.mpr fun Z hZ => ?_)
  rw [QMCLeafB.maxcut_objective_eq A Z (QMCLeafB.transpose_eq_of_posSemidef hZ.1)]
  have h := B.lo_sound Z hZ
  have hV : QMCLeafB.V A = ∑ i, ∑ j, A i j := rfl
  rw [hV]
  linarith

/-! ## 5.  Running the bisection -/

/-- `k` bisection steps, each one engine call. -/
noncomputable def iter {A : Matrix (Fin n) (Fin n) ℝ}
    (eng : ∀ t : ℚ, Answer A t) (B : Brack A) : ℕ → Brack A
  | 0 => B
  | (k + 1) => step eng (iter eng B k)

/-- After `k` steps the bracket width is `(hi₀ − lo₀)/2^k`. -/
theorem iter_width {A : Matrix (Fin n) (Fin n) ℝ}
    (eng : ∀ t : ℚ, Answer A t) (B : Brack A) :
    ∀ k : ℕ, (iter eng B k).hi - (iter eng B k).lo = (B.hi - B.lo) / 2 ^ k
  | 0 => by simp [iter]
  | (k + 1) => by
      have hrec : (iter eng B (k + 1)).hi - (iter eng B (k + 1)).lo
          = ((iter eng B k).hi - (iter eng B k).lo) / 2 := by
        simp only [iter]
        exact step_width eng (iter eng B k)
      rw [hrec, iter_width eng B k, div_div, pow_succ]

/-- A step never raises the witnessed endpoint. -/
theorem step_hi_le {A : Matrix (Fin n) (Fin n) ℝ}
    (eng : ∀ t : ℚ, Answer A t) (B : Brack A) : (step eng B).hi ≤ B.hi := by
  unfold step
  split
  · linarith [B.lo_le_hi]
  · exact le_rfl

/-- The witnessed endpoint never rises above where it started, so the final `hi` is at most the
starting one — this is what makes the leaf's `L` nonnegative. -/
theorem hi_le_start {A : Matrix (Fin n) (Fin n) ℝ}
    (eng : ∀ t : ℚ, Answer A t) (B : Brack A) :
    ∀ k : ℕ, (iter eng B k).hi ≤ B.hi
  | 0 => by simp [iter]
  | (k + 1) => by
      have h1 : (iter eng B (k + 1)).hi ≤ (iter eng B k).hi := by
        simp only [iter]
        exact step_hi_le eng (iter eng B k)
      exact h1.trans (hi_le_start eng B k)

/-- **The driver, abstractly.**  From any start bracket and any engine answering every rational
threshold, `k` bisection steps leave the SDP value between the two ends of the bracket. -/
theorem driver_bounds {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S)
    (eng : ∀ t : ℚ, Answer A t) (B₀ : Brack A) (k : ℕ) :
    (QMCLeafB.V A - ((iter eng B₀ k).hi : ℝ)) / 4 ≤ S ∧
      S ≤ (QMCLeafB.V A - ((iter eng B₀ k).lo : ℝ)) / 4 :=
  ⟨lower_bound hS (iter eng B₀ k), upper_bound hS (iter eng B₀ k)⟩

/-! ## 6.  The concrete start bracket -/

/-- **The start bracket for graph data.**  For entrywise nonnegative weights with zero diagonal
and total weight the rational `R`:

* the identity matrix is a feasible witness whose trace is the diagonal sum `0`, so `hi = 0`;
* `lo = -R` is refuted by `neg_abs_sum_le_trace`.

Hence the initial width is `R` itself — there is no free numerical constant to choose. -/
noncomputable def startBrack {A : Matrix (Fin n) (Fin n) ℝ}
    (_hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0) (R : ℚ)
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ)) : Brack A where
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
    norm_num
  lo_sound := by
    intro Z hZ
    have h := neg_abs_sum_le_trace A Z hZ
    have hcast : ((-R : ℚ) : ℝ) = -(R : ℝ) := by push_cast; ring
    rw [hcast, ← hRabs]
    exact h

/-- The start bracket's width is the total weight. -/
theorem startBrack_width {A : Matrix (Fin n) (Fin n) ℝ}
    (hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0) (R : ℚ)
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ)) :
    (startBrack hAn hAz R hRabs).hi - (startBrack hAn hAz R hRabs).lo = R := by
  simp [startBrack]

/-! ## 7.  Leaf B: thirteen engine calls -/

/-- **The leaf's lower value from the threshold driver.**  For entrywise nonnegative data with
zero diagonal and rational total weight `R = V A`, thirteen bisection steps give a *rational*
`Lq` with

    0 ≤ Lq,   Lq ≤ S,   S − Lq ≤ R/20000,

where `S` is any realization of the SDP value.  The only non-numerical input is the engine's
per-threshold answer `eng`; the number of calls is the `13` in the definition of `Bk`, and
`R/32768 ≤ R/20000` is where `2^13 ≥ 5000` is used. -/
theorem leafB_threshold_driver {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S)
    (hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0)
    (R : ℚ) (hR : QMCLeafB.V A = (R : ℝ))
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ))
    (eng : ∀ t : ℚ, Answer A t) :
    ∃ Lq : ℚ, 0 ≤ Lq ∧ (Lq : ℝ) ≤ S ∧ S - (Lq : ℝ) ≤ (R : ℝ) / 20000 := by
  -- the starting bracket and thirteen steps of the bisection
  set B₀ : Brack A := startBrack hAn hAz R hRabs with hB₀
  set Bk : Brack A := iter eng B₀ 13 with hBk
  -- the total weight is a nonnegative rational
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
  -- the two sides of the sandwich at the final bracket
  have hlow : (QMCLeafB.V A - (Bk.hi : ℝ)) / 4 ≤ S := (driver_bounds hS eng B₀ 13).1
  have hup : S ≤ (QMCLeafB.V A - (Bk.lo : ℝ)) / 4 := (driver_bounds hS eng B₀ 13).2
  refine ⟨(R - Bk.hi) / 4, ?_, ?_, ?_⟩
  · -- nonnegative
    have h1 : Bk.hi ≤ R := hhi.trans hR0q
    linarith
  · -- below the SDP value
    have hcast : (((R - Bk.hi) / 4 : ℚ) : ℝ) = ((R : ℝ) - (Bk.hi : ℝ)) / 4 := by
      push_cast; ring
    rw [hcast, ← hR]
    exact hlow
  · -- and the gap is at most `R/2^13/4 ≤ R/20000`
    have hcast : (((R - Bk.hi) / 4 : ℚ) : ℝ) = ((R : ℝ) - (Bk.hi : ℝ)) / 4 := by
      push_cast; ring
    rw [hcast, ← hR]
    have hstep : (R : ℝ) / 2 ^ 13 / 4 ≤ (R : ℝ) / 20000 := by
      have h2 : (R : ℝ) / 2 ^ 13 / 4 = (R : ℝ) / 32768 := by
        rw [div_div]
        norm_num
      rw [h2]
      nlinarith [hR0]
    nlinarith [hup, hwR]

/-- **The leaf's bound at the graph instance.**  With the rational total weight
`2 ∑ₑ wₑ` of the weighted graph, the driver's `R/20000` is exactly the campaign's `W/10000`. -/
theorem leafB_threshold_driver_wMatrix (G : QuantumMaxCutEnergy.Input) {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S)
    (eng : ∀ t : ℚ, Answer (QMCLeafB.wMatrix G) t) :
    ∃ Lq : ℚ, 0 ≤ Lq ∧ (Lq : ℝ) ≤ S ∧
      S - (Lq : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  -- the rational total weight of the instance
  set Rq : ℚ := 2 * ∑ e, ((G.weights e : ℚ≥0) : ℚ) with hRq
  have hV : QMCLeafB.V (QMCLeafB.wMatrix G) = (Rq : ℝ) := by
    rw [QMCLeafB.V_wMatrix, hRq]
    push_cast
    ring
  have hRabs : (∑ i, ∑ j, |QMCLeafB.wMatrix G i j|) = (Rq : ℝ) := by
    rw [← hV]
    show (∑ i, ∑ j, |QMCLeafB.wMatrix G i j|)
        = ∑ i, ∑ j, QMCLeafB.wMatrix G i j
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      abs_of_nonneg (QMCLeafB.wMatrix_nonneg G i j)
  have hAn : ∀ i j, 0 ≤ QMCLeafB.wMatrix G i j := QMCLeafB.wMatrix_nonneg G
  have hAz : ∀ i, QMCLeafB.wMatrix G i i = 0 := fun i => QMCLeafB.wMatrix_apply_of_eq
  obtain ⟨Lq, h0, h1, h2⟩ :=
    leafB_threshold_driver hS hAn hAz Rq hV hRabs eng
  refine ⟨Lq, h0, h1, ?_⟩
  have hR20000 : (Rq : ℝ) / 20000 = (∑ e, (G.weights e : ℝ)) / 10000 := by
    rw [hRq]
    push_cast
    ring
  linarith [h2, hR20000.le, hR20000.ge]

end QMCLeafB.ThresholdDriver

/-! ## 8.  How the other bricks' outputs enter the `Answer` type

The two constructors are not decorative:

* the **dual** side of a certified display pair (`QMCLeafB.RoundingOut.DisplayPair`,
  `hy : (diagonal y + A).PosSemidef`) refutes every threshold below `-∑ᵢ yᵢ` — this is how the
  rounding-out factory's dual certificate feeds the driver without any extra analysis;
* an explicitly **feasible** point (the rational primal of a display pair, read over `ℝ` by
  `QMCLeafB.CastBridge.realPrimalFeasible`) is the `feasible` constructor directly.

The section also records that the contract is inhabited, so the driver's hypothesis is not
vacuous. -/

namespace QMCLeafB.ThresholdDriver
variable {n : ℕ}

/-- **A dual-feasible point refutes every threshold below `−∑ᵢ yᵢ`.**  For unit-diagonal
semidefinite `Z`, `0 ≤ tr((diagonal y + A) Z) = ∑ᵢ yᵢ + tr(A Z)`, so `tr(A Z) ≥ −∑ᵢ yᵢ`. -/
theorem dual_refutes {A : Matrix (Fin n) (Fin n) ℝ} {y : Fin n → ℝ} {t : ℚ}
    (hy : (Matrix.diagonal y + A).PosSemidef) (hyt : (t : ℝ) ≤ -(∑ i, y i)) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD Z → (t : ℝ) ≤ (A * Z).trace := by
  intro Z hZ
  have h0 : 0 ≤ ((Matrix.diagonal y + A) * Z).trace :=
    QMCLeafB.psd_trace_mul_nonneg hy hZ.1
  rw [Matrix.add_mul, Matrix.trace_add, QMCLeafB.trace_diagonal_mul_of_unitDiag y hZ.2] at h0
  linarith

/-- The dual certificate of a display pair, in the driver's `infeasible` constructor. -/
def answer_of_dual {A : Matrix (Fin n) (Fin n) ℝ} {y : Fin n → ℝ} {t : ℚ}
    (hy : (Matrix.diagonal y + A).PosSemidef) (hyt : (t : ℝ) ≤ -(∑ i, y i)) :
    Answer A t :=
  Answer.infeasible (dual_refutes hy hyt)

/-- A feasible point, in the driver's `feasible` constructor. -/
def answer_of_primal {A : Matrix (Fin n) (Fin n) ℝ} {X : Matrix (Fin n) (Fin n) ℝ}
    {t : ℚ} (hX : ModernConvex.Relaxations.IsUnitDiagPSD X)
    (htr : (A * X).trace ≤ (t : ℝ)) : Answer A t :=
  Answer.feasible X hX htr

/-- The contract `∀ t, Answer A t` is inhabited: the zero matrix is answered at every rational
threshold, by the identity on the feasible side and by the trivial refutation on the other. -/
def answer_zero (t : ℚ) : Answer (0 : Matrix (Fin n) (Fin n) ℝ) t := by
  by_cases h : (0 : ℚ) ≤ t
  · refine answer_of_primal (A := 0) isUnitDiagPSD_one ?_
    have hcast : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
    simpa using hcast
  · refine Answer.infeasible fun Z _ => ?_
    have hcast : (t : ℝ) ≤ 0 := by
      have h' : t ≤ 0 := le_of_not_ge h
      exact_mod_cast h'
    simpa using hcast

/-! ### A nondegenerate instance: the single edge

`A = [[0,1],[1,0]]` has `tr(A Z) = 2 Z₀₁ ≥ −2` for every feasible `Z`, with equality at the
rank-one point `Z = (1,−1)(1,−1)ᵀ`.  So every threshold `t ≤ −2` is refuted, and `t = −2`
already carries a witness: both constructors are inhabited on the same instance, and the
contract's "at least one holds" is tight exactly at `−2`. -/

/-- The single-edge weight matrix. -/
def edgeA : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; 1, 0]

/-- The rank-one witness `(1,−1)(1,−1)ᵀ`. -/
def edgeW : Matrix (Fin 2) (Fin 2) ℝ := !![(1 : ℝ), -1; -1, 1]

theorem edgeA_mul (X : Matrix (Fin 2) (Fin 2) ℝ) :
    edgeA * X = !![X 1 0, X 1 1; X 0 0, X 0 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [edgeA, Matrix.mul_apply, Fin.sum_univ_two]

theorem edgeA_trace (X : Matrix (Fin 2) (Fin 2) ℝ) (hsym : X 1 0 = X 0 1) :
    (edgeA * X).trace = 2 * X 0 1 := by
  rw [edgeA_mul]
  simp [Matrix.trace, Fin.sum_univ_two, hsym]
  ring

def edgeA_refute {t : ℚ} (ht : t ≤ -2) : Answer edgeA t := by
  refine Answer.infeasible fun Z hZ => ?_
  have hsym : Z 1 0 = Z 0 1 := by
    have h := congrFun (congrFun (QMCLeafB.transpose_eq_of_posSemidef hZ.1) 1) 0
    simpa [Matrix.transpose_apply] using h.symm
  have h1 : -1 ≤ Z 0 1 := neg_one_le_apply hZ.1 hZ.2 0 1
  have hcast : (t : ℝ) ≤ -2 := by exact_mod_cast ht
  rw [edgeA_trace Z hsym]
  linarith

/-- `edgeW` is positive semidefinite because its quadratic form is `(x₀ − x₁)²`. -/
theorem posSemidef_edgeW : edgeW.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [edgeW]
  · intro x
    have hx : (star x) ⬝ᵥ (edgeW *ᵥ x) = (x 0 - x 1) ^ 2 := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two, edgeW,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val_fin_one,
        Matrix.empty_val', Matrix.cons_val']
      ring
    rw [hx]
    exact sq_nonneg _

/-- The witness at the tight threshold: `tr(A Z) = −2` there. -/
def edgeA_feasible : Answer edgeA (-2 : ℚ) := by
  refine Answer.feasible edgeW ⟨posSemidef_edgeW, ?_⟩ ?_
  · intro i
    fin_cases i <;> simp [edgeW]
  · have hsym : edgeW 1 0 = edgeW 0 1 := by simp [edgeW]
    rw [edgeA_trace edgeW hsym]
    norm_num [edgeW]

/-- Both constructors on the single edge: the contract is non-vacuous and the two branches
meet exactly at `t = −2`. -/
theorem edgeA_answers :
    (∀ t : ℚ, t ≤ -2 → Nonempty (Answer edgeA t)) ∧ Nonempty (Answer edgeA (-2)) :=
  ⟨fun t ht => ⟨edgeA_refute (t := t) ht⟩, ⟨edgeA_feasible⟩⟩

/-- **The engine only has to answer thresholds in `[−R, 0]`.**  For nonnegative zero-diagonal
data with rational total weight `R`, the general contract `∀ t, Answer A t` follows from answers
on the interval `[−R, 0]` alone:

* above `0` the identity matrix is a witness, because `tr(A · 1)` is the diagonal sum, which is
  `0` here;
* below `−R` the `ℓ¹` bound `neg_abs_sum_le_trace` refutes the threshold outright.

So the ellipsoid engine never has to reason about thresholds outside the meaningful range: the
thirteen bisection queries all lie in the start bracket `[−R, 0]` anyway. -/
def answer_of_range {A : Matrix (Fin n) (Fin n) ℝ} (hAz : ∀ i, A i i = 0) {R : ℚ}
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ))
    (eng : ∀ t : ℚ, -R ≤ t → t ≤ 0 → Answer A t) : ∀ t : ℚ, Answer A t := by
  intro t
  by_cases hlow : t ≤ -R
  · refine Answer.infeasible fun Z hZ => ?_
    have hb := neg_abs_sum_le_trace A Z hZ
    have hcast : (t : ℝ) ≤ ((-R : ℚ) : ℝ) := by exact_mod_cast hlow
    have hcastR : ((-R : ℚ) : ℝ) = -(R : ℝ) := by push_cast; ring
    rw [hcastR, ← hRabs] at hcast
    linarith
  · have hlow' : -R ≤ t := le_of_not_ge hlow
    by_cases hhigh : t ≤ 0
    · exact eng t hlow' hhigh
    · have hhigh' : (0 : ℚ) < t := lt_of_not_ge hhigh
      refine Answer.feasible 1 isUnitDiagPSD_one ?_
      rw [trace_mul_one]
      have hzero : (∑ i, A i i) = 0 := Finset.sum_eq_zero fun i _ => hAz i
      rw [hzero]
      have h0 : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast hhigh'.le
      simpa using h0

/-- **The leaf's bound from a range-restricted engine**: the version the ellipsoid brick should
target, since all thirteen queries lie in `[−R, 0]`. -/
theorem leafB_threshold_driver_range {A : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S)
    (hAn : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0) (R : ℚ)
    (hR : QMCLeafB.V A = (R : ℝ))
    (hRabs : (∑ i, ∑ j, |A i j|) = (R : ℝ))
    (eng : ∀ t : ℚ, -R ≤ t → t ≤ 0 → Answer A t) :
    ∃ Lq : ℚ, 0 ≤ Lq ∧ (Lq : ℝ) ≤ S ∧ S - (Lq : ℝ) ≤ (R : ℝ) / 20000 :=
  leafB_threshold_driver hS hAn hAz R hR hRabs (answer_of_range hAz hRabs eng)

end QMCLeafB.ThresholdDriver

#print axioms QMCLeafB.ThresholdDriver.neg_abs_sum_le_trace
#print axioms QMCLeafB.ThresholdDriver.step_width
#print axioms QMCLeafB.ThresholdDriver.lower_bound
#print axioms QMCLeafB.ThresholdDriver.upper_bound
#print axioms QMCLeafB.ThresholdDriver.iter_width
#print axioms QMCLeafB.ThresholdDriver.hi_le_start
#print axioms QMCLeafB.ThresholdDriver.driver_bounds
#print axioms QMCLeafB.ThresholdDriver.startBrack_width
#print axioms QMCLeafB.ThresholdDriver.leafB_threshold_driver
#print axioms QMCLeafB.ThresholdDriver.leafB_threshold_driver_wMatrix
#print axioms QMCLeafB.ThresholdDriver.dual_refutes
#print axioms QMCLeafB.ThresholdDriver.answer_zero
#print axioms QMCLeafB.ThresholdDriver.edgeA_trace
#print axioms QMCLeafB.ThresholdDriver.posSemidef_edgeW
#print axioms QMCLeafB.ThresholdDriver.edgeA_answers
#print axioms QMCLeafB.ThresholdDriver.answer_of_range
#print axioms QMCLeafB.ThresholdDriver.leafB_threshold_driver_range


