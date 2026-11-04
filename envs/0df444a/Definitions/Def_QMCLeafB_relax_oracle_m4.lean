-- Prove2me | Definitions.Def_QMCLeafB_relax_oracle_m4
-- name    : QMCLeafB_relax_oracle_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:37:05.566679+00:00
-- url     : https://prove2.me/theorems/337ab17d-101d-4d03-86c5-8893868327b6
-- title:
--   QMCLeafB relax_oracle_m4
-- statement:
--   # brick-relaxed-oracle — the strict-body (relaxed) separation oracle
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sep_oracle_m1
import Definitions.Def_QMCLeafB_ball_floor
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_RoundingOut
import Definitions.Def_QMCLeafB_Core
/-
# brick-relaxed-oracle — the strict-body (relaxed) separation oracle

Leaf B phase 10, member m4, direction d2 (supersedes the phase-9 file of the same module name).

## Why this file exists

`Check_sim_loop_m6.simulate_refuted_sound` — the refutation half of the leaf's verdict — does not
run the GLS loop on the exact threshold body.  It runs it on the **relaxation**

    W = QMCLeafB.BallFloor.relaxBodyLE A u δ
      = { X | -(δ/2)·‖x‖² ≤ qf X x,  |X_ii - 1| ≤ δ/4,  ⟪A,X⟫ ≤ u + δ/2 },     u = t - εr,

which is the strict body `{X : X ⪰ 0, diag X = 1, ⟪A,X⟫ ≤ t - εr}` widened in all three
coordinates (that widening is what carries the ball of radius `δ/(8(c_A+1))` around every
strict-body point, hence what makes the determinant floor apply).  Its `hcutδ` hypothesis asks for
cuts that contain `W`:

    ∀ z ∈ Boundary.relaxBall A (t-εr) δ M,  -(δ k) ≤ cutCR cd k ⬝ᵥ (z - Cat … k).

`QMCLeafB.SepOracle.sepOracle` supplies cuts that contain the **exact** body
`Body A t = {⟪A,X⟫ ≥ t}` — the opposite trace direction, with no margins.  It cannot be used
here; and nothing in the tree consumes `GoodCut`/`OkReport`/`relaxBodyLE` at all, so this
interface was simply missing.  This file supplies it.

## What is proved

At a rational centre `cX`, threshold `u` and tolerance `δ > 0`:

* `RelaxMem A cX u δ` — **the loop's `ok`**: the centre lies in the relaxation, with computed
  margins (`psd_margin`, `diag_near`, `trace_le`).  This is the branch that stops the run and
  hands the primal point to the rounding-out/finalization chain.
* `RelaxOk A cX u δ` — the *feasibility-side* ledger of `SepOracle.OkReport` shape
  (`t - δ/2 ≤ ⟪A,cX⟫` instead of `⟪A,cX⟫ ≤ t + δ/2`); `relaxOk_toReport` turns it into
  `SepOracle.OkReport n A u cX` **verbatim**, so the `sep-oracle` brick's object is reachable.
`RelaxCut A cX u δ` — rational data `(normal, margin > 0)` with
`-margin ≤ ⟪normal, X - cX⟫` for **every real** `X ∈ W`.  All the loop ever stores is
`(normal, margin)`, and this is exactly its contract.

The three branches, each with the exact rational margin (no square roots, no eigenvalues):

| branch | hypothesis | normal | margin |
|---|---|---|---|
| psd   | `qf cX v < -(δ/2)‖v‖²`            | `v vᵀ`               | `-qf cX v - (δ/2)‖v‖²` |
| diag  | `δ/4 < \|cX_ii - 1\|`              | `sign(1-cX_ii)·e_i e_iᵀ` | `\|cX_ii - 1\| - δ/4` |
| trace | `u + δ/2 < ⟪A,cX⟫`                | `-A`                 | `⟪A,cX⟫ - (u + δ/2)` |

`relaxMem_or_cut` is the totality theorem: **every** rational centre is either inside the
relaxation or separated from it, so the loop never gets stuck.  `relaxOracle` is the same
dichotomy as a **computable `def`**: the psd branch is `SepOracle.splitOfTranspose` (the exact
rational LDLᵀ pivot recursion) applied to the shifted matrix `cX + (δ/2)·1`, the diagonal branch is
the *summed indicator* cut of §4.5 (`diagExcess`, `diagNormalSum`, `diagMarginSum`, `diagSumCut` —
the total excess `∑_i max 0 (|cX_ii - 1| - δ/4)` as the margin), and the branch selection is the
rational test `diagMarginSum cX δ = 0`.  No `Classical.choice` occurs in it, so it can be compiled
into the round program; §4.5's `diagMarginSum_eq_zero_iff` identifies its test with the diagonal
clause of `RelaxMem` exactly.

`RelaxCut.separates_flat` / `separates_ball` / `separates_hcutδ` restate a cut in the flat
`Fin (n*n)` shape that `CutData.c` and `hcutδ` speak, with `frob_eq_flat_dot` the bridge, and
**`hcutδ_of_relaxCuts` (§5.5) is `Check_sim_loop_m6.simulate_refuted_sound`'s `hcutδ` hypothesis**
verbatim, from the oracle's cut verdicts on the failed rounds.

## The `ok` side is consumed too (§6)

`RelaxMem` alone is not enough for `simulate_feasible_sound`'s `hcert`: that needs a *genuine*
unit-diagonal semidefinite point at threshold `t + εw`.  `relaxMem_witness` produces one from the
centre `cX + (δ/2)·1` by `Check_RoundingOut`'s exact rational diagonal rounding (cost
`roundCost A (3δ/4)`) and `Check_CastBridge`'s rational-to-real PSD transfer, and
`hcert_of_relaxMem` states it in the loop's slack arithmetic
(`roundCost A (3δ/4) + δ/2 - εr ≤ εw`).

Note on the trace branch: since `W` carries an **upper** trace bound, the normal is `-A`, unlike
`SepOracle.traceCut`.  This is the one place the relaxed oracle differs from the exact one, and it
is why `sepOracle`'s output cannot be reused.

## What this file does not do

* it does not choose the centres: the state recursion `k ↦ cX_k` (with the dyadic enclosure of the
  irrational GLS centre) is still missing — see the module note of `Check_sim_loop_m6`;
* it does not give the `Automatic.Poly` program: the oracle is a `def` over the plain rational
  data, but the surrounding loop still needs the height ledger of `PolyLoop` (`brick-pivot-program`,
  `brick-sim-ground`);
* it does not assemble the recorded `CutData` stream (`p` is the round program's witness of
  `A_k p = c_k` and `rho` its depth); `hcutδ_of_relaxCuts` consumes the stream once the round
  program supplies those two fields and the centre equation.

No `sorry`, no `axiom`; the audit at the end shows the standard three.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators
open Matrix

namespace QMCLeafB.RelaxOracle

open QMCLeafB.SepOracle

variable {n : ℕ}
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## 0.  Two bilinearity/cast lemmas -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem frob_smul_left (c : K) (C X : Matrix (Fin n) (Fin n) K) :
    frob (c • C) X = c * frob C X := by
  rw [frob, frob, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem castMat_smul (c : ℚ) (M : Matrix (Fin n) (Fin n) ℚ) :
    castMat (c • M) = ((c : ℚ) : ℝ) • castMat M := by
  ext a b
  simp [castMat, Matrix.smul_apply, smul_eq_mul]

theorem signOf_cases (q : ℚ) : signOf q = 1 ∨ signOf q = -1 ∨ signOf q = 0 := by
  unfold signOf
  split_ifs <;> simp

/-! ## 1.  The two `ok` bundles -/

/-- **The loop's `ok`: the centre lies in the relaxation.**  Every field is a rational,
machine-checkable margin; `trace_le` is `relaxBodyLE`'s own (upper) trace bound. -/
structure RelaxMem (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) : Prop where
  δ_pos : 0 < δ
  psd_margin : ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qf cX x
  diag_near : ∀ i, |cX i i - 1| ≤ δ / 4
  trace_le : frob A cX ≤ u + δ / 2

/-- **The feasibility-side ledger** (`SepOracle.OkReport`'s shape): the centre is PSD-close,
diagonal-close and *above* the threshold.  Used by the finalization/rounding chain; note it is
*not* the loop's stop condition (`RelaxMem` is). -/
structure RelaxOk (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) : Prop where
  δ_pos : 0 < δ
  psd_margin : ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qf cX x
  diag_near : ∀ i, |cX i i - 1| ≤ δ / 4
  trace_ok : u + δ / 2 ≤ frob A cX

/-- **`RelaxOk` is the finalization's ledger**: `SepOracle.OkReport` at the same `(A, u, cX)` and
the same tolerance. -/
theorem relaxOk_toReport {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (h : RelaxOk A cX u δ) : Nonempty (OkReport n A u cX) :=
  ⟨{ δ := δ, δ_pos := h.δ_pos, psd_margin := h.psd_margin, diag_near := h.diag_near,
     trace_near := by linarith [h.δ_pos, h.trace_ok] }⟩

/-! ## 2.  The cut verdict: the loop's contract, verbatim -/

/-- **A cut containing the relaxation.**  `normal` and `margin` are rational data (all the loop
stores); `separates` is the geometric fact, quantified over the *real* relaxation — this is
`Check_sim_loop_m6.simulate_refuted_sound`'s `hcutδ` at `u = t - εr`. -/
structure RelaxCut (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) where
  normal : Matrix (Fin n) (Fin n) ℚ
  margin : ℚ
  margin_pos : 0 < margin
  separates : ∀ X : Matrix (Fin n) (Fin n) ℝ,
    QMCLeafB.BallFloor.relaxBodyLE (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) X →
      -((margin : ℚ) : ℝ) ≤ frob (castMat normal) (X - castMat cX)

variable {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}

/-! ### 2.1  The psd branch -/

/-- **psd branch.**  A violated relaxed quadratic form at the rational vector `v` is a halfspace:
the rank-one normal `v vᵀ` contains the relaxation with the exact margin
`-qf cX v - (δ/2)‖v‖² > 0`. -/
def psdCutOf {v : Fin n → ℚ}
    (h : qf cX v < -(δ / 2) * (∑ i, v i ^ 2)) : RelaxCut A cX u δ :=
  ⟨vecMulVec v v, -qf cX v - (δ / 2) * (∑ i, v i ^ 2), by linarith, by
  intro X hX
  obtain ⟨hpsd, -, -⟩ := hX
  have hcast : qf (castMat cX) (fun i => ((v i : ℚ) : ℝ)) = ((qf cX v : ℚ) : ℝ) := by
    simpa [castMat] using qf_map (Rat.castHom ℝ) cX v
  have hb : -((((δ : ℚ) : ℝ)) / 2) * (∑ i, ((v i : ℚ) : ℝ) ^ 2)
      ≤ qf X (fun i => ((v i : ℚ) : ℝ)) := by
    simpa only [QMCLeafB.BallFloor.qfR, QMCLeafB.SepOracle.qf]
      using hpsd (fun i => ((v i : ℚ) : ℝ))
  have hc : ((qf cX v : ℚ) : ℝ)
      < -((((δ : ℚ) : ℝ)) / 2) * (∑ i, ((v i : ℚ) : ℝ) ^ 2) := by
    have h1 : ((qf cX v : ℚ) : ℝ) < ((-(δ / 2) * (∑ i, v i ^ 2) : ℚ) : ℝ) := by
      exact_mod_cast h
    have h2 : ((-(δ / 2) * (∑ i, v i ^ 2) : ℚ) : ℝ)
        = -((((δ : ℚ) : ℝ)) / 2) * (∑ i, ((v i : ℚ) : ℝ) ^ 2) := by push_cast; ring
    rwa [h2] at h1
  have hkey : frob (castMat (vecMulVec v v)) (X - castMat cX)
      = qf X (fun i => ((v i : ℚ) : ℝ)) - ((qf cX v : ℚ) : ℝ) := by
    rw [castMat_vecMulVec, frob_sub, ← qf_eq_frob X (fun i => ((v i : ℚ) : ℝ)),
      ← qf_eq_frob (castMat cX) (fun i => ((v i : ℚ) : ℝ)), hcast]
  rw [hkey]
  push_cast
  linarith⟩

theorem psdBranch {v : Fin n → ℚ}
    (h : qf cX v < -(δ / 2) * (∑ i, v i ^ 2)) :
    Nonempty (RelaxCut A cX u δ) :=
  ⟨psdCutOf h⟩

/-! ### 2.2  The diagonal branch -/

/-- The coordinate normal `sign(1 - cX_ii) · e_i e_iᵀ`. -/
def diagNormal (cX : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : Matrix (Fin n) (Fin n) ℚ :=
  signOf (1 - cX i i) • vecMulVec (delta i) (delta i)

/-- The pairing of the coordinate normal with any matrix reads off the diagonal entry. -/
theorem frob_diagNormal {cX : Matrix (Fin n) (Fin n) ℚ} (i : Fin n)
    (Y : Matrix (Fin n) (Fin n) ℝ) :
    frob (castMat (diagNormal cX i)) Y = (((signOf (1 - cX i i) : ℚ)) : ℝ) * Y i i := by
  have hcast : castMat (diagNormal cX i)
      = (((signOf (1 - cX i i) : ℚ)) : ℝ) •
        castMat (vecMulVec (delta (K := ℚ) i) (delta (K := ℚ) i)) := by
    rw [diagNormal, castMat_smul]
  rw [hcast, frob_smul_left, castMat_delta, ← qf_eq_frob Y (delta (K := ℝ) i), qf_delta]

/-- **Diagonal branch.**  A diagonal entry off by more than `δ/4` is separated by the coordinate
normal, with margin `|cX_ii - 1| - δ/4 > 0`. -/
def diagCutOf (i : Fin n) (h : δ / 4 < |cX i i - 1|) : RelaxCut A cX u δ :=
  ⟨diagNormal cX i, |cX i i - 1| - δ / 4, by linarith, by
  intro X hX
  obtain ⟨-, hdiag, -⟩ := hX
  have hs : signOf (1 - cX i i) = 1 ∨ signOf (1 - cX i i) = -1 ∨ signOf (1 - cX i i) = 0 :=
    signOf_cases _
  have hsmul : signOf (1 - cX i i) * (1 - cX i i) = |cX i i - 1| := by
    rw [signOf_mul_self, abs_sub_comm]
  have hcastC : (((signOf (1 - cX i i) : ℚ)) : ℝ) * (1 - ((cX i i : ℚ) : ℝ))
      = |((cX i i : ℚ) : ℝ) - 1| := by
    have h' := congrArg (fun q : ℚ => ((q : ℚ) : ℝ)) hsmul
    push_cast at h'
    exact h'
  have hstep : -|X i i - 1| ≤ (((signOf (1 - cX i i) : ℚ)) : ℝ) * (X i i - 1) := by
    rcases hs with h1 | h1 | h1
    · rw [h1]; push_cast; linarith [neg_abs_le (X i i - 1)]
    · rw [h1]; push_cast; linarith [le_abs_self (X i i - 1)]
    · rw [h1]; push_cast; linarith [abs_nonneg (X i i - 1)]
  have hXii : |X i i - 1| ≤ (((δ : ℚ)) : ℝ) / 4 := hdiag i
  have hR : (((δ : ℚ)) : ℝ) / 4 < |((cX i i : ℚ) : ℝ) - 1| := by
    have h1 : (((δ / 4 : ℚ)) : ℝ) < ((|cX i i - 1| : ℚ) : ℝ) := by
      exact_mod_cast h
    have h2 : (((δ : ℚ)) : ℝ) / 4 = ((δ / 4 : ℚ) : ℝ) := by push_cast; ring
    have h3 : ((|cX i i - 1| : ℚ) : ℝ) = |((cX i i : ℚ) : ℝ) - 1| := by push_cast; ring
    rw [h2, ← h3]
    exact h1
  have hkey : frob (castMat (diagNormal cX i)) (X - castMat cX)
      = (((signOf (1 - cX i i) : ℚ)) : ℝ) * (X i i - 1)
        + (((signOf (1 - cX i i) : ℚ)) : ℝ) * (1 - ((cX i i : ℚ) : ℝ)) := by
    rw [frob_sub, frob_diagNormal i X, frob_diagNormal i (castMat cX)]
    have hcc : castMat cX i i = ((cX i i : ℚ) : ℝ) := rfl
    rw [hcc]; ring
  rw [hkey, hcastC]
  push_cast
  linarith⟩

theorem diagBranch (i : Fin n) (h : δ / 4 < |cX i i - 1|) :
    Nonempty (RelaxCut A cX u δ) :=
  ⟨diagCutOf i h⟩

/-! ### 2.3  The trace branches (the flipped normal)

`relaxBodyLE` bounds the objective from **above** (`⟪A,X⟫ ≤ u + δ/2`), so the trace cut's normal is
`-A`.  Both sides of the test give a valid cut, with opposite margins; the loop uses the *high*
side (`⟪A,cX⟫ > u + δ/2`, the centre is above the relaxation) together with `RelaxMem`. -/

/-- **Trace branch, high side**: the centre is above the relaxation's trace bound. -/
def traceHighCutOf (h : u + δ / 2 < frob A cX) : RelaxCut A cX u δ :=
  ⟨-A, frob A cX - (u + δ / 2), by linarith, by
  intro X hX
  have hR : ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 < ((frob A cX : ℚ) : ℝ) := by
    have h1 : ((u + δ / 2 : ℚ) : ℝ) < ((frob A cX : ℚ) : ℝ) := by exact_mod_cast h
    have h2 : ((u + δ / 2 : ℚ) : ℝ) = ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 := by
      push_cast; ring
    rwa [h2] at h1
  obtain ⟨-, -, htr⟩ := hX
  have hcastA : frob (castMat A) X ≤ ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 := htr
  have hcastc : frob (castMat A) (castMat cX) = ((frob A cX : ℚ) : ℝ) :=
    frob_map (Rat.castHom ℝ) A cX
  have hneg : castMat (-A) = -castMat A := by
    ext a b; simp [castMat]
  have hkey : frob (castMat (-A)) (X - castMat cX)
      = -(frob (castMat A) X - frob (castMat A) (castMat cX)) := by
    rw [hneg, frob_neg_left, frob_sub]
  rw [hkey, hcastc]
  push_cast
  linarith⟩

/-- **Trace branch, low side**: the mirror image (the centre is below the trace bound). -/
def traceLowCutOf (h : frob A cX < u + δ / 2) : RelaxCut A cX u δ :=
  ⟨-A, u + δ / 2 - frob A cX, by linarith, by
  intro X hX
  obtain ⟨-, -, htr⟩ := hX
  have hcastA : frob (castMat A) X ≤ ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 := htr
  have hcastc : frob (castMat A) (castMat cX) = ((frob A cX : ℚ) : ℝ) :=
    frob_map (Rat.castHom ℝ) A cX
  have hneg : castMat (-A) = -castMat A := by
    ext a b; simp [castMat]
  have hkey : frob (castMat (-A)) (X - castMat cX)
      = -(frob (castMat A) X - frob (castMat A) (castMat cX)) := by
    rw [hneg, frob_neg_left, frob_sub]
  rw [hkey, hcastc]
  push_cast
  linarith⟩

/-! ## 3.  Totality -/

/-- **The relaxed oracle is total (loop form).**  Every rational centre is either inside the
relaxation (the `ok` that stops the run) or separated from it by an explicit rational cut. -/
theorem relaxMem_or_cut (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) (hδ : 0 < δ) :
    RelaxMem A cX u δ ∨ Nonempty (RelaxCut A cX u δ) := by
  by_cases htr : frob A cX ≤ u + δ / 2
  · by_cases hdiag : ∀ i, |cX i i - 1| ≤ δ / 4
    · by_cases hpsd : ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qf cX x
      · exact Or.inl ⟨hδ, hpsd, hdiag, htr⟩
      · obtain ⟨v, hv⟩ := not_forall.mp hpsd
        exact Or.inr (psdBranch (lt_of_not_ge hv))
    · obtain ⟨i, hi⟩ := not_forall.mp hdiag
      exact Or.inr (diagBranch i (lt_of_not_ge hi))
  · exact Or.inr ⟨traceHighCutOf (lt_of_not_ge htr)⟩

/-- **The same totality on the feasibility side**, with `RelaxOk` (the `OkReport` ledger) as the
positive verdict. -/
theorem relaxOk_or_cut (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) (hδ : 0 < δ) :
    RelaxOk A cX u δ ∨ Nonempty (RelaxCut A cX u δ) := by
  by_cases htr : u + δ / 2 ≤ frob A cX
  · by_cases hdiag : ∀ i, |cX i i - 1| ≤ δ / 4
    · by_cases hpsd : ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qf cX x
      · exact Or.inl ⟨hδ, hpsd, hdiag, htr⟩
      · obtain ⟨v, hv⟩ := not_forall.mp hpsd
        exact Or.inr (psdBranch (lt_of_not_ge hv))
    · obtain ⟨i, hi⟩ := not_forall.mp hdiag
      exact Or.inr (diagBranch i (lt_of_not_ge hi))
  · exact Or.inr ⟨traceLowCutOf (lt_of_not_ge htr)⟩

/-! ## 4.  The flat (`Fin (n*n)`) shape that `CutData` and `hcutδ` speak -/

/-- Row-major flattening of a rational matrix (the normal the loop stores). -/
noncomputable def flatQ (X : Matrix (Fin n) (Fin n) ℚ) : Fin (n * n) → ℚ :=
  fun k => X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- **The pairing is the flat dot product of the row-major flattenings.** -/
theorem frob_eq_flat_dot (N M : Matrix (Fin n) (Fin n) ℝ) :
    frob N M = ∑ k : Fin (n * n),
      QMCLeafB.AnswerProducer.flat N k * QMCLeafB.AnswerProducer.flat M k := by
  calc frob N M = ∑ i, ∑ j, N i j * M i j := rfl
    _ = ∑ p : Fin n × Fin n, N p.1 p.2 * M p.1 p.2 :=
        (Fintype.sum_prod_type (f := fun p : Fin n × Fin n => N p.1 p.2 * M p.1 p.2)).symm
    _ = ∑ k : Fin (n * n),
          QMCLeafB.AnswerProducer.flat N k * QMCLeafB.AnswerProducer.flat M k := by
        rw [← Equiv.sum_comp finProdFinEquiv
          (fun k : Fin (n * n) =>
            QMCLeafB.AnswerProducer.flat N k * QMCLeafB.AnswerProducer.flat M k)]
        exact Finset.sum_congr rfl (fun p _ => by simp [QMCLeafB.AnswerProducer.flat])

/-- **A cut in the loop's flat shape.**  For a flat point `z` whose unflattening lies in the
relaxation, `-margin ≤ normal ⬝ᵥ (z - centre)`, with the rational normal and margin read off the
cut (`CutData.c` and `Cat` are exactly these two flat vectors). -/
theorem RelaxCut.separates_flat (C : RelaxCut A cX u δ) :
    ∀ z : Fin (n * n) → ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ)
        (QMCLeafB.Boundary.unflat z) →
      -((C.margin : ℚ) : ℝ) ≤
        (fun k : Fin (n * n) => ((flatQ C.normal k : ℚ) : ℝ)) ⬝ᵥ
          (z - QMCLeafB.AnswerProducer.flat (castMat cX)) := by
  intro z hz
  have h := C.separates (QMCLeafB.Boundary.unflat z) hz
  rw [frob_eq_flat_dot] at h
  have h2 : (QMCLeafB.AnswerProducer.flat (QMCLeafB.Boundary.unflat z - castMat cX))
      = z - QMCLeafB.AnswerProducer.flat (castMat cX) := by
    rw [QMCLeafB.Boundary.flat_sub, QMCLeafB.Boundary.flat_unflat]
  rw [h2] at h
  have h3 : (∑ k : Fin (n * n), QMCLeafB.AnswerProducer.flat (castMat C.normal) k
        * (z - QMCLeafB.AnswerProducer.flat (castMat cX)) k)
      = ∑ k : Fin (n * n), (((flatQ C.normal k : ℚ)) : ℝ)
        * (z - QMCLeafB.AnswerProducer.flat (castMat cX)) k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [flatQ, QMCLeafB.AnswerProducer.flat, castMat]
  rw [h3] at h
  rwa [dotProduct]

/-- The same on the campaign's own `Boundary.relaxBall` — the set `hcutδ` quantifies over. -/
theorem RelaxCut.separates_ball (C : RelaxCut A cX u δ) (M : ℝ) :
    ∀ z : Fin (n * n) → ℝ,
      z ∈ QMCLeafB.Boundary.relaxBall (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) M →
      -((C.margin : ℚ) : ℝ) ≤
        (fun k : Fin (n * n) => ((flatQ C.normal k : ℚ) : ℝ)) ⬝ᵥ
          (z - QMCLeafB.AnswerProducer.flat (castMat cX)) :=
  fun z hz => C.separates_flat z hz.1

variable {t εr : ℚ}

/-- **Pinned to `hcutδ`**: with the loop's own instantiation `u = t - εr`, a cut of the relaxation
at tolerance `δq` gives `Check_sim_loop_m6.simulate_refuted_sound`'s hypothesis, reading the cut's
`margin` as the round's `δ k`, its flat normal as `cutCR cd k`, and the flat centre as `Cat … k`. -/
theorem RelaxCut.separates_hcutδ (C : RelaxCut A cX (t - εr) δ) (M : ℝ) :
    ∀ z : Fin (n * n) → ℝ,
      z ∈ QMCLeafB.Boundary.relaxBall (castMat A) (((t : ℚ) : ℝ) - ((εr : ℚ) : ℝ))
        ((δ : ℚ) : ℝ) M →
      -((C.margin : ℚ) : ℝ) ≤
        (fun k : Fin (n * n) => ((flatQ C.normal k : ℚ) : ℝ)) ⬝ᵥ
          (z - QMCLeafB.AnswerProducer.flat (castMat cX)) := by
  have hu : (((t - εr : ℚ)) : ℝ) = ((t : ℚ) : ℝ) - ((εr : ℚ) : ℝ) := by push_cast; ring
  intro z hz
  exact C.separates_ball M z (by rw [← hu] at hz; exact hz)

/-! ## 4.5  A computable diagonal branch: the summed indicator cut

`diagCutOf` separates at a *found* index `i`, and that search is the only place `Classical.choice`
entered the oracle.  The summed form needs none: with

    diagExcess cX δ i     = max 0 (|cX_ii - 1| - δ/4)
    diagNormalSum cX δ i  = if δ/4 < |cX_ii - 1| then sign(1 - cX_ii) else 0

the normal `diagonal (diagNormalSum cX δ)` separates the relaxation with margin
`diagMarginSum cX δ = ∑ i, diagExcess cX δ i`: it is the *sum* of the coordinate cuts that bite,
and the margin is positive exactly when some diagonal entry of the centre is further than `δ/4`
from `1`.  Both quantities are decided by rational comparisons, and the complementary test
`diagMarginSum cX δ = 0` is *exactly* the diagonal clause of the `ok` bundle — so the branch
selection is a computation. -/

/-- The excess of one diagonal slack over the relaxation's tolerance, `max 0 (|cX_ii - 1| - δ/4)`.
-/
def diagExcess (cX : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) (i : Fin n) : ℚ :=
  if δ / 4 < |cX i i - 1| then |cX i i - 1| - δ / 4 else 0

/-- The summed diagonal cut's normal, in diagonal (vector) form: `sign(1 - cX_ii)` on the
coordinates that exceed the tolerance, `0` on the others. -/
def diagNormalSum (cX : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) : Fin n → ℚ :=
  fun i => if δ / 4 < |cX i i - 1| then signOf (1 - cX i i) else 0

/-- The summed diagonal cut's margin: the total excess `∑ i, max 0 (|cX_ii - 1| - δ/4)`. -/
def diagMarginSum (cX : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) : ℚ :=
  ∑ i, diagExcess cX δ i

theorem diagExcess_nonneg (cX : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) (i : Fin n) :
    0 ≤ diagExcess cX δ i := by
  unfold diagExcess
  split_ifs with h
  · linarith
  · exact le_rfl

theorem diagMarginSum_nonneg (cX : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) :
    0 ≤ diagMarginSum cX δ :=
  Finset.sum_nonneg fun i _ => diagExcess_nonneg cX δ i

/-- A single excess vanishes exactly when the coordinate is inside the tolerance. -/
theorem diagExcess_eq_zero_iff {cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ} {i : Fin n} :
    diagExcess cX δ i = 0 ↔ |cX i i - 1| ≤ δ / 4 := by
  unfold diagExcess
  split_ifs with h
  · constructor
    · intro h0; linarith
    · intro h0; linarith
  · constructor
    · intro _; linarith
    · intro _; rfl

/-- **The summed margin vanishes exactly on the `ok` diagonal clause.** -/
theorem diagMarginSum_eq_zero_iff (cX : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) :
    diagMarginSum cX δ = 0 ↔ ∀ i, |cX i i - 1| ≤ δ / 4 := by
  constructor
  · intro h i
    have hle : diagExcess cX δ i ≤ diagMarginSum cX δ := by
      rw [diagMarginSum]
      exact Finset.single_le_sum (f := fun j => diagExcess cX δ j)
        (fun j _ => diagExcess_nonneg cX δ j) (Finset.mem_univ i)
    have h0 : diagExcess cX δ i = 0 :=
      le_antisymm (by rw [h] at hle; exact hle) (diagExcess_nonneg cX δ i)
    exact diagExcess_eq_zero_iff.mp h0
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    exact diagExcess_eq_zero_iff.mpr (h i)

/-- The Frobenius pairing with a real diagonal matrix reads off the diagonal. -/
theorem frob_diagonal_R (s : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ) :
    frob (diagonal s) Y = ∑ i, s i * Y i i := by
  rw [frob]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Matrix.diagonal_apply_ne, Ne.symm hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Casting a rational diagonal matrix is the real diagonal matrix of the casts. -/
theorem castMat_diagonal (s : Fin n → ℚ) :
    castMat (diagonal s) = diagonal (fun i => ((s i : ℚ) : ℝ)) := by
  ext i j
  rw [castMat_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- **The per-coordinate bound behind the summed cut.**  Inside the relaxation the `i`-th diagonal
entry is within `δ/4` of `1`, so the `i`-th summand of the pairing is at least the negative of the
excess — and is `0` on the coordinates that do not bite. -/
theorem perIndex_diagSum {cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ}
    {X : Matrix (Fin n) (Fin n) ℝ} (i : Fin n)
    (hX : |X i i - 1| ≤ (((δ : ℚ)) : ℝ) / 4) :
    -(((diagExcess cX δ i : ℚ)) : ℝ)
      ≤ (((diagNormalSum cX δ i : ℚ)) : ℝ) * (X i i - ((cX i i : ℚ) : ℝ)) := by
  by_cases h : δ / 4 < |cX i i - 1|
  · have hs : diagNormalSum cX δ i = signOf (1 - cX i i) := by simp [diagNormalSum, h]
    have he : diagExcess cX δ i = |cX i i - 1| - δ / 4 := by simp [diagExcess, h]
    have hsgn : signOf (1 - cX i i) = 1 ∨ signOf (1 - cX i i) = -1 ∨ signOf (1 - cX i i) = 0 :=
      signOf_cases _
    have hsmul : signOf (1 - cX i i) * (1 - cX i i) = |cX i i - 1| := by
      rw [signOf_mul_self, abs_sub_comm]
    have hcastC : (((signOf (1 - cX i i) : ℚ)) : ℝ) * (1 - ((cX i i : ℚ) : ℝ))
        = |((cX i i : ℚ) : ℝ) - 1| := by
      have h' := congrArg (fun q : ℚ => ((q : ℚ) : ℝ)) hsmul
      push_cast at h'
      exact h'
    have hstep : -|X i i - 1| ≤ (((signOf (1 - cX i i) : ℚ)) : ℝ) * (X i i - 1) := by
      rcases hsgn with h1 | h1 | h1
      · rw [h1]; push_cast; linarith [neg_abs_le (X i i - 1)]
      · rw [h1]; push_cast; linarith [le_abs_self (X i i - 1)]
      · rw [h1]; push_cast; linarith [abs_nonneg (X i i - 1)]
    have hsplit : (((signOf (1 - cX i i) : ℚ)) : ℝ) * (X i i - ((cX i i : ℚ) : ℝ))
        = (((signOf (1 - cX i i) : ℚ)) : ℝ) * (X i i - 1)
          + |((cX i i : ℚ) : ℝ) - 1| := by
      rw [← hcastC]; ring
    have hexcess : (((diagExcess cX δ i : ℚ)) : ℝ)
        = |((cX i i : ℚ) : ℝ) - 1| - (((δ : ℚ)) : ℝ) / 4 := by
      rw [he]; push_cast; ring
    have hR : (((δ : ℚ)) : ℝ) / 4 < |((cX i i : ℚ) : ℝ) - 1| := by
      have h1 : (((δ / 4 : ℚ)) : ℝ) < ((|cX i i - 1| : ℚ) : ℝ) := by exact_mod_cast h
      have h2 : (((δ : ℚ)) : ℝ) / 4 = ((δ / 4 : ℚ) : ℝ) := by push_cast; ring
      have h3 : ((|cX i i - 1| : ℚ) : ℝ) = |((cX i i : ℚ) : ℝ) - 1| := by push_cast; ring
      rw [h2, ← h3]
      exact h1
    rw [hs, hsplit, hexcess]
    linarith
  · have hs : diagNormalSum cX δ i = 0 := by simp [diagNormalSum, h]
    have he : diagExcess cX δ i = 0 := by simp [diagExcess, h]
    rw [hs, he]
    simp

/-- **The summed diagonal cut**: it contains the whole relaxation, with margin `diagMarginSum`,
and its data are computed by rational comparisons and `signOf` alone. -/
def diagSumCut {A : Matrix (Fin n) (Fin n) ℚ} {cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (h : 0 < diagMarginSum cX δ) : RelaxCut A cX u δ where
  normal := diagonal (diagNormalSum cX δ)
  margin := diagMarginSum cX δ
  margin_pos := h
  separates := by
    intro X hX
    obtain ⟨-, hdiag, -⟩ := hX
    have hcast : castMat (diagonal (diagNormalSum cX δ))
        = diagonal (fun i => (((diagNormalSum cX δ i : ℚ)) : ℝ)) := castMat_diagonal _
    have hsub : ∀ i : Fin n, (X - castMat cX) i i = X i i - ((cX i i : ℚ) : ℝ) := by
      intro i
      simp [Matrix.sub_apply, castMat]
    rw [hcast, frob_diagonal_R]
    calc ∑ i, (((diagNormalSum cX δ i : ℚ)) : ℝ) * (X - castMat cX) i i
        = ∑ i, (((diagNormalSum cX δ i : ℚ)) : ℝ) * (X i i - ((cX i i : ℚ) : ℝ)) :=
          Finset.sum_congr rfl fun i _ => by rw [hsub i]
      _ ≥ ∑ i, -(((diagExcess cX δ i : ℚ)) : ℝ) :=
          Finset.sum_le_sum fun i _ => perIndex_diagSum i (hdiag i)
      _ = -(((diagMarginSum cX δ : ℚ)) : ℝ) := by
          rw [diagMarginSum, Finset.sum_neg_distrib]
          push_cast
          rfl

theorem diagBranchSum {A : Matrix (Fin n) (Fin n) ℚ} {cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (h : 0 < diagMarginSum cX δ) : Nonempty (RelaxCut A cX u δ) :=
  ⟨diagSumCut h⟩

/-! ## 5.  The oracle as a computation

All three branches are decided by rational comparisons and the exact rational pivot split of
the summed-diagonal section, so the oracle is a `def`, not merely a `noncomputable` object: the psd
branch is `SepOracle.splitOfTranspose` applied to the *shifted* matrix `cX + (δ/2)·1` (whose
quadratic form is `qf cX x + (δ/2)‖x‖²`, `qf_shift`), the diagonal branch is the summed indicator cut
(§4.5), and the trace branch is the flipped normal `-A`. -/

/-- The oracle's verdict type: the loop's `ok` or a cut. -/
inductive RelaxResponse (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) : Type where
  | mem (h : RelaxMem A cX u δ) : RelaxResponse A cX u δ
  | cut (C : RelaxCut A cX u δ) : RelaxResponse A cX u δ

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem qf_one (x : Fin n → K) : qf (1 : Matrix (Fin n) (Fin n) K) x = ∑ i, x i ^ 2 := by
  simp [qf, dotProduct, pow_two]

/-- The shifted quadratic form: `qf (cX + (δ/2)·1) x = qf cX x + (δ/2)‖x‖²`. -/
theorem qf_shift (cX : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) (x : Fin n → ℚ) :
    qf (cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ)) x
      = qf cX x + (δ / 2) * (∑ i, x i ^ 2) := by
  rw [qf_add, qf_smulQ, qf_one]

/-- Symmetry of the shifted centre `cX + (δ/2)·1` (the matrix the psd branch splits). -/
theorem shift_symm {cX : Matrix (Fin n) (Fin n) ℚ} (hs : cXᵀ = cX) (δ : ℚ) :
    (cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ))ᵀ
      = cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hs]

/-- **The computable relaxed separation oracle.**  Every branch is decided by rational
comparisons: the trace test is `frob A cX ≤ u + δ/2` (`RelaxMem`'s clause, its negation giving the
flipped normal `-A`), the diagonal test is `diagMarginSum cX δ = 0` (`ok`) against the summed
indicator cut (`cut`), and the psd branch is the exact rational pivot split of the shifted matrix
`cX + (δ/2)·1` by `SepOracle.splitOfTranspose`, the LDLᵀ recursion.  No `Classical.choice` occurs
in the returned data: this is a genuine computation. -/
def relaxOracle (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) (hδ : 0 < δ) (hs : cXᵀ = cX) : RelaxResponse A cX u δ :=
  if htr : frob A cX ≤ u + δ / 2 then
    if hdiag : diagMarginSum cX δ = 0 then
      match splitOfTranspose n (cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ))
        (shift_symm hs δ) with
      | Split.psd m C hC =>
          RelaxResponse.mem
            ⟨hδ, fun x => by
              have h0 := premise_of_check C (cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ)) hC x
              rw [qf_shift] at h0
              linarith,
             (diagMarginSum_eq_zero_iff cX δ).mp hdiag, htr⟩
      | Split.violated v hv =>
          RelaxResponse.cut (psdCutOf (v := v) (by
            rw [qf_shift] at hv
            linarith))
    else
      RelaxResponse.cut (diagSumCut (A := A) (cX := cX) (u := u) (δ := δ)
        (lt_of_le_of_ne (diagMarginSum_nonneg cX δ) (Ne.symm hdiag)))
  else
    RelaxResponse.cut (traceHighCutOf (A := A) (cX := cX) (u := u) (δ := δ)
      (lt_of_not_ge htr))

/-- Every verdict of the oracle is `ok` or a cut. -/
theorem RelaxResponse.toSum {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} :
    RelaxResponse A cX u δ → (RelaxMem A cX u δ ∨ Nonempty (RelaxCut A cX u δ))
  | .mem h => Or.inl h
  | .cut C => Or.inr ⟨C⟩

/-- **The computable oracle is correct**: its verdict is the loop's `ok` or a cut containing the
relaxation. -/
theorem relaxOracle_spec (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) (hδ : 0 < δ) (hs : cXᵀ = cX) :
    RelaxMem A cX u δ ∨ Nonempty (RelaxCut A cX u δ) :=
  (relaxOracle A cX u δ hδ hs).toSum



/-! ## 5.5  The flat bridge: `hcutδ` from a family of cuts

`Check_sim_loop_m6.simulate_refuted_sound` consumes the cut family through one hypothesis,

    hcutδ : ∀ k, k < K·m → ok k = false → ∀ z,
      z ∈ Boundary.relaxBall A (t − εr) δq M →
        −(δ k) ≤ cutCR cd k ⬝ᵥ (z − Cat (n·n) 0 cd k),

where `cd : ℕ → CutData (n·n)` is the loop's *recorded* cut stream and `Cat` its centre.  It asks for
a cut only on the rounds that reported a cut (`ok k = false`), which is exactly what the oracle
supplies.  `hcutδ_of_relaxCuts` below is that hypothesis, from the oracle's verdicts plus the two
identifications that tie the recorded stream to the oracle's data:

* `(cd k).c = flatQ (C k hok).normal` — the recorded normal *is* the cut's flat normal;
* `Cat (n·n) 0 cd k = flat (cX k)` — the recorded centre *is* the oracle's centre,

with `mg k = (C k hok).margin` the round's margin.  This is the interface between this brick and the
refuted half of `brick-verdict-sound`. -/

/-- **`hcutδ` from the oracle's cut verdicts.** -/
theorem hcutδ_of_relaxCuts {A : Matrix (Fin n) (Fin n) ℚ} {t εr δq : ℚ} {M : ℝ}
    (ok : ℕ → Bool) (T : ℕ) (cX : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (C : ∀ k, ok k = false → RelaxCut A (cX k) (t - εr) δq)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n)) (mg : ℕ → ℚ)
    (hnorm : ∀ k (hok : ok k = false), (cd k).c = flatQ (C k hok).normal)
    (hmg : ∀ k (hok : ok k = false), mg k = (C k hok).margin)
    (hctr : ∀ k, QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
      = QMCLeafB.AnswerProducer.flat (castMat (cX k))) :
    ∀ k, k < T → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (castMat A) ((t : ℝ) - (εr : ℝ)) ((δq : ℚ) : ℝ) M →
      -(((mg k : ℚ)) : ℝ) ≤
        QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
          (z - QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k) := by
  intro k _ hok z hz
  have hu : ((t : ℝ) - (εr : ℝ)) = (((t - εr : ℚ)) : ℝ) := by push_cast; ring
  rw [hu] at hz
  have h := (C k hok).separates_ball M z hz
  have hc : QMCLeafB.EngineIterates.cutCR cd k
      = fun i => (((flatQ (C k hok).normal) i : ℚ) : ℝ) := by
    funext i
    simp [QMCLeafB.EngineIterates.cutCR, hnorm k hok]
  rw [hc, hctr k, hmg k hok]
  exact h

/-! ## 6.  The `ok` branch yields a witness (the loop's `hcert`)

`Check_sim_loop_m6.simulate_feasible_sound` needs, at every round that reports `ok`, a
**genuine** unit-diagonal positive semidefinite *real* matrix whose objective is at most
`t + εw`.  `RelaxMem` only gives a rational centre inside the relaxation.  Two compiled bricks
close the gap, exactly and without square roots:

* `Check_RoundingOut`'s `roundDiag` fixes the diagonal by the closed-form rational congruence
  `c_i = 2/(1+X_ii)` plus a compensating diagonal shift; it preserves the rational PSD test
  (`roundDiag_ratPSD`) and costs at most `roundCost A ν` in the objective (`trace_roundDiag_le`);
* `Check_CastBridge`'s `posSemidef_of_rat_tests` turns the rational PSD test into
  `Matrix.PosSemidef` over `ℝ`.

The shift `X₀ = cX + (δ/2)·1` is what makes `X₀` rationally PSD (`qf_shift`) and its diagonal
land in `[1+δ/4, 1+3δ/4]`, i.e. within `ν = 3δ/4` of `1`.  On `wMatrix` (`A` symmetric, zero
diagonal, so `tr A = 0`) the shift does not move the objective at all. -/

/-- The trace of a cast product is the cast of the rational trace. -/
theorem trace_castM (A Y : Matrix (Fin n) (Fin n) ℚ) :
    (QMCLeafB.CastBridge.castM A * QMCLeafB.CastBridge.castM Y).trace
      = (((A * Y).trace : ℚ) : ℝ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    QMCLeafB.CastBridge.castM_apply]
  push_cast
  rfl

/-- The diagonal of the shifted centre. -/
theorem shift_diag (cX : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) (i : Fin n) :
    (cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ)) i i = cX i i + δ / 2 := by
  simp [Matrix.add_apply, Matrix.smul_apply]

/-- The shifted centre's trace against a zero-diagonal `A` is the centre's own. -/
theorem trace_mul_shift {A cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ}
    (hA0 : ∀ i, A i i = 0) :
    (A * (cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ))).trace = (A * cX).trace := by
  have h1 : A * (cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ))
      = A * cX + (δ / 2) • (A * (1 : Matrix (Fin n) (Fin n) ℚ)) := by
    rw [Matrix.mul_add, Matrix.mul_smul]
  rw [h1, Matrix.trace_add, Matrix.trace_smul, Matrix.mul_one]
  have h2 : A.trace = 0 := by
    rw [Matrix.trace]
    exact Finset.sum_eq_zero fun i _ => hA0 i
  rw [h2, smul_eq_mul, mul_zero, add_zero]

/-- **`RelaxMem` produces a witness**, with the rounding cost explicit. -/
theorem relaxMem_witness {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (h : RelaxMem A cX u δ) (hAsym : Aᵀ = A) (hCsym : cXᵀ = cX) (hA0 : ∀ i, A i i = 0) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.CastBridge.castM A * X).trace
          ≤ (((u + δ / 2 + QMCLeafB.RoundingOut.roundCost A (3 * δ / 4) : ℚ)) : ℝ) := by
  classical
  obtain ⟨hδ0, hpsd, hdiag, htr⟩ := h
  set ν : ℚ := 3 * δ / 4 with hν
  have hν0 : 0 ≤ ν := by have := hδ0; simp only [hν]; linarith
  set X0 : Matrix (Fin n) (Fin n) ℚ := cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ) with hX0
  have hX0sym : X0ᵀ = X0 := by
    rw [hX0, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hCsym]
  have hX0p : QMCLeafB.RoundingOut.RatPSD X0 := by
    intro x
    have h1 : QMCLeafB.RoundingOut.qf X0 x
        = QMCLeafB.SepOracle.qf cX x + (δ / 2) * (∑ i, x i ^ 2) := by
      rw [hX0]; exact qf_shift cX δ x
    rw [h1]
    linarith [hpsd x]
  have hX0diag : ∀ i, |X0 i i - 1| ≤ ν := by
    intro i
    have h1 : X0 i i = cX i i + δ / 2 := by rw [hX0]; exact shift_diag cX δ i
    have h2 : |cX i i - 1| ≤ δ / 4 := hdiag i
    rw [h1, hν]
    have h3 : cX i i + δ / 2 - 1 = (cX i i - 1) + δ / 2 := by ring
    rw [h3]
    calc |(cX i i - 1) + δ / 2| ≤ |cX i i - 1| + |δ / 2| := abs_add_le _ _
      _ ≤ δ / 4 + δ / 2 := by
          have h4 : |δ / 2| = δ / 2 := abs_of_pos (by linarith)
          rw [h4]; linarith
      _ = 3 * δ / 4 := by ring
  set Y : Matrix (Fin n) (Fin n) ℚ := QMCLeafB.RoundingOut.roundDiag X0 with hY
  have hYsym : Yᵀ = Y := by rw [hY]; exact QMCLeafB.RoundingOut.roundDiag_symm hX0sym
  have hYp : QMCLeafB.RoundingOut.RatPSD Y := by
    rw [hY]; exact QMCLeafB.RoundingOut.roundDiag_ratPSD hX0p
  have hYdiag : ∀ i, Y i i = 1 := by
    intro i; rw [hY]; exact QMCLeafB.RoundingOut.roundDiag_diag X0 i
  have hYtr : (A * Y).trace ≤ (A * X0).trace + QMCLeafB.RoundingOut.roundCost A ν := by
    have h' := QMCLeafB.RoundingOut.trace_roundDiag_le (A := A) (X := X0) (ν := ν)
      hX0sym hX0p hX0diag hν0
    rw [← hY] at h'
    exact h'
  have hX0tr : (A * X0).trace = (A * cX).trace := by rw [hX0]; exact trace_mul_shift hA0
  have hftr : (A * cX).trace = frob A cX := (frob_eq_trace hCsym A).symm
  refine ⟨QMCLeafB.CastBridge.castM Y, ?_, ?_⟩
  · refine ⟨QMCLeafB.CastBridge.posSemidef_of_rat_tests Y hYsym hYp, fun i => ?_⟩
    rw [QMCLeafB.CastBridge.castM_apply, hYdiag i]
    norm_num
  · rw [trace_castM]
    have hbound : (A * Y).trace ≤ u + δ / 2 + QMCLeafB.RoundingOut.roundCost A ν := by
      calc (A * Y).trace ≤ (A * X0).trace + QMCLeafB.RoundingOut.roundCost A ν := hYtr
        _ = (A * cX).trace + QMCLeafB.RoundingOut.roundCost A ν := by rw [hX0tr]
        _ ≤ u + δ / 2 + QMCLeafB.RoundingOut.roundCost A ν := by linarith [hftr ▸ htr]
    exact_mod_cast hbound

/-- **The `hcert` slot of `simulate_feasible_sound`**: at the loop's slack `u = t - εr`, an `ok`
centre yields a feasible point at the witnessed threshold `t + εw`, provided the rounding cost
plus `δ/2` minus the refutation slack fits in `εw`. -/
theorem hcert_of_relaxMem {A cX : Matrix (Fin n) (Fin n) ℚ} {t εr δ εw : ℚ}
    (h : RelaxMem A cX (t - εr) δ) (hAsym : Aᵀ = A) (hCsym : cXᵀ = cX)
    (hA0 : ∀ i, A i i = 0)
    (hbudget : QMCLeafB.RoundingOut.roundCost A (3 * δ / 4) + δ / 2 - εr ≤ εw) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.CastBridge.castM A * X).trace ≤ ((t : ℚ) : ℝ) + ((εw : ℚ) : ℝ) := by
  obtain ⟨X, hX, htr⟩ := relaxMem_witness h hAsym hCsym hA0
  refine ⟨X, hX, ?_⟩
  refine le_trans htr ?_
  have : (t - εr) + δ / 2 + QMCLeafB.RoundingOut.roundCost A (3 * δ / 4) ≤ t + εw := by
    linarith
  have h2 : ((((t - εr) + δ / 2 + QMCLeafB.RoundingOut.roundCost A (3 * δ / 4) : ℚ)) : ℝ)
      ≤ ((t : ℚ) : ℝ) + ((εw : ℚ) : ℝ) := by exact_mod_cast this
  calc ((((t - εr) + δ / 2 + QMCLeafB.RoundingOut.roundCost A (3 * δ / 4) : ℚ)) : ℝ)
      ≤ ((t : ℚ) : ℝ) + ((εw : ℚ) : ℝ) := h2
    _ = (↑t : ℝ) + (↑εw : ℝ) := rfl

/-! ## 7.  Non-vacuity: both verdicts are realized

The interface is only useful if it is inhabited on both sides.  On `n = 2`:

* `RelaxMem` holds for the identity centre below the threshold (`A = 0`, `cX = 1`, `u = 0`,
  `δ = 1`), so the loop's `ok` is reachable;
* `RelaxCut` holds there for the centre `2·1` (diagonal branch, margin `3/4`), and for a
  non-diagonal `A` with the centre `5·1` (trace branch, margin `19/2`) — so the cut branch is
  reachable too, and `relaxMem_or_cut` is a genuine dichotomy, not a vacuous one. -/

/-- The loop's `ok` is inhabited. -/
theorem relaxMem_example :
    RelaxMem (0 : Matrix (Fin 2) (Fin 2) ℚ) (1 : Matrix (Fin 2) (Fin 2) ℚ) 0 1 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro x
    rw [qf_one]
    have h : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    linarith
  · intro i
    have h : (1 : Matrix (Fin 2) (Fin 2) ℚ) i i = 1 := by simp
    rw [h]; norm_num
  · simp [frob]

/-- The diagonal cut is inhabited (and its margin is the exact slack `|2-1| - 1/4 = 3/4`). -/
theorem diagCut_witness :
    Nonempty (RelaxCut (0 : Matrix (Fin 2) (Fin 2) ℚ)
      (2 • (1 : Matrix (Fin 2) (Fin 2) ℚ)) 0 1) :=
  ⟨diagCutOf (A := 0) (cX := 2 • (1 : Matrix (Fin 2) (Fin 2) ℚ)) (u := 0) (δ := 1) 0 (by
    simp [Matrix.smul_apply]; norm_num)⟩

/-- The trace cut is inhabited for a genuinely off-diagonal `A` and a centre with
`⟪A,cX⟫ = 10` (margin `10 - 1/2 = 19/2`). -/
theorem traceCut_witness :
    Nonempty (RelaxCut (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)
      (!![5, 5; 5, 5] : Matrix (Fin 2) (Fin 2) ℚ) 0 1) :=
  ⟨traceHighCutOf (A := !![0, 1; 1, 0]) (cX := !![5, 5; 5, 5])
    (u := 0) (δ := 1) (by
      rw [frob]
      simp only [Fin.sum_univ_two]
      norm_num)⟩

/-! ## 8.  Axiom audit -/
#print axioms QMCLeafB.RelaxOracle.diagExcess_eq_zero_iff
#print axioms QMCLeafB.RelaxOracle.diagMarginSum_eq_zero_iff
#print axioms QMCLeafB.RelaxOracle.perIndex_diagSum
#print axioms QMCLeafB.RelaxOracle.diagSumCut
#print axioms QMCLeafB.RelaxOracle.shift_symm
#print axioms QMCLeafB.RelaxOracle.hcutδ_of_relaxCuts

#print axioms QMCLeafB.RelaxOracle.frob_smul_left
#print axioms QMCLeafB.RelaxOracle.relaxOk_toReport
#print axioms QMCLeafB.RelaxOracle.psdCutOf
#print axioms QMCLeafB.RelaxOracle.frob_diagNormal
#print axioms QMCLeafB.RelaxOracle.diagCutOf
#print axioms QMCLeafB.RelaxOracle.traceHighCutOf
#print axioms QMCLeafB.RelaxOracle.traceLowCutOf
#print axioms QMCLeafB.RelaxOracle.relaxMem_or_cut
#print axioms QMCLeafB.RelaxOracle.relaxOk_or_cut
#print axioms QMCLeafB.RelaxOracle.psdBranch
#print axioms QMCLeafB.RelaxOracle.diagBranch
#print axioms QMCLeafB.RelaxOracle.frob_eq_flat_dot
#print axioms QMCLeafB.RelaxOracle.RelaxCut.separates_flat
#print axioms QMCLeafB.RelaxOracle.RelaxCut.separates_ball
#print axioms QMCLeafB.RelaxOracle.RelaxCut.separates_hcutδ
#print axioms QMCLeafB.RelaxOracle.relaxOracle
#print axioms QMCLeafB.RelaxOracle.relaxOracle_spec
#print axioms QMCLeafB.RelaxOracle.relaxMem_example
#print axioms QMCLeafB.RelaxOracle.diagCut_witness
#print axioms QMCLeafB.RelaxOracle.trace_castM
#print axioms QMCLeafB.RelaxOracle.trace_mul_shift
#print axioms QMCLeafB.RelaxOracle.relaxMem_witness
#print axioms QMCLeafB.RelaxOracle.hcert_of_relaxMem
#print axioms QMCLeafB.RelaxOracle.traceCut_witness

end QMCLeafB.RelaxOracle


