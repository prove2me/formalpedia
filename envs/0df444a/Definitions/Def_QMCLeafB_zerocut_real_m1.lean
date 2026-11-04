-- Prove2me | Definitions.Def_QMCLeafB_zerocut_real_m1
-- name    : QMCLeafB_zerocut_real_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:15:51.380961+00:00
-- url     : https://prove2.me/theorems/259f3e4e-bee3-473f-a1ea-b7e668d8bb6b
-- title:
--   QMCLeafB zerocut_real_m1
-- statement:
--   # leaf B phase 13 — `zerocut` (swarm `smw17fqzz`, member m1, direction d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_verdict_sound
/-
# leaf B phase 13 — `zerocut` (swarm `smw17fqzz`, member m1, direction d6)

**Why this file exists.**  `QMCLeafB.VerdictSound.RunData` couples the recorded cut margin and the
recorded depth (`hcheck : del² ≤ rho²·sigmaQ`), and the shelf's only explicit halving lemma
(`SimLoop.halving_time_explicit`) is stated at depth **zero**.  A positive margin therefore forces a
positive depth, which no shelf lemma covers.  The resolved design is the *central cut*: `del = 0`,
`rho = 0`, `rmax = 0`, `m = 4(n·n)` — `SimLoop.central_run_budget` / `Aat_vol_below_central` are
built for exactly that regime.

A central cut needs the separation `0 ≤ normal ⬝ (X - centre)` — margin **zero**, not the `-margin ≤`
that `Check_relax_oracle_m4`'s `RelaxCut` exposes.  (`Cut0` in
`Solutions/Check_zero_margin_cut_m1.lean` supplies it there, in that file's vocabulary.)

**But `Check_relax_oracle_m4` cannot be imported together with the closing stroke.**  Its closure
contains `Solutions.Check_CastBridge` (`QMCLeafB.CastBridge.castM`), while the closing stroke's
closure contains `Solutions.MergeAll3_m8`, which re-declares `castM` at the same name; Lean refuses
the second import ("environment already contains '…castM'").  So the cut facts have to exist in the
**verdict closure** too, which is what this file provides: the same three branches, re-proved
against `QMCLeafB.BallFloor.frob` / `relaxBodyLE` with a locally defined rational cast `castQ` and
the verdict closure's own `QMCLeafB.EngineIterates.qf`.

Contents:

* `castQ`, `flatQ` — rational matrix cast and row-major flattening (the `Cat`/`cutCR` coordinates);
* `ZeroCut A cX u δ` — rational normal `normal` plus the zero-margin separation
  `0 ≤ frob (castQ normal) (X - castQ cX)` over `relaxBodyLE A u δ`;
* `psdCut`, `diagCut`, `traceCut` — the three branches the loop uses (the *low* trace side is
  excluded: the centre satisfies the trace bound there, so it does not separate);
* `psdCut_normal_ne_zero`, `diagCut_normal_ne_zero`, `traceCut_normal_ne_zero`, `flatQ_ne_zero` —
  `RunData.hcne`;
* `ZeroCut.separates_flat` — the flat dot-product form, `0 ≤ normal ⬝ᵥ (z - centre)` on
  `Boundary.relaxBall`, i.e. `RunData.hcut` at `del k := 0` verbatim.

No `sorry`, no `axiom`; audits at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.VerdictCut

open QMCLeafB.BallFloor

/-! ## 1.  Coordinates -/

/-- Row-major flattening of a rational matrix — the loop's `CutData.c` coordinates. -/
def flatQ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℚ) : Fin (n * n) → ℚ :=
  fun k => N (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The rational-to-real cast of a matrix (local copy; the closing stroke's closure has no other). -/
def castQ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((N i j : ℚ) : ℝ)

/-- The flat form of the cast is the cast of the flat form. -/
theorem flatQ_cast {n : ℕ} (N : Matrix (Fin n) (Fin n) ℚ) :
    (fun m => ((flatQ N m : ℚ) : ℝ)) = QMCLeafB.AnswerProducer.flat (castQ N) := by
  funext k
  simp [flatQ, castQ, QMCLeafB.AnswerProducer.flat]

/-- A non-zero rational matrix has a non-zero flat vector (`RunData.hcne`). -/
theorem flatQ_ne_zero {n : ℕ} {N : Matrix (Fin n) (Fin n) ℚ} (h : N ≠ 0) : flatQ N ≠ 0 := by
  intro h0
  apply h
  ext i j
  have h1 := congrFun h0 (finProdFinEquiv (i, j))
  simpa [flatQ, Equiv.symm_apply_apply] using h1

theorem frob_sub' {n : ℕ} (N X Y : Matrix (Fin n) (Fin n) ℝ) :
    frob N (X - Y) = frob N X - frob N Y := by
  simp only [frob, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem frob_smul_left' {n : ℕ} (c : ℝ) (C X : Matrix (Fin n) (Fin n) ℝ) :
    frob (c • C) X = c * frob C X := by
  simp only [frob]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem frob_neg_left' {n : ℕ} (C X : Matrix (Fin n) (Fin n) ℝ) :
    frob (-C) X = -frob C X := by
  have h : (-C : Matrix (Fin n) (Fin n) ℝ) = (-1 : ℝ) • C := by
    ext a b
    simp
  rw [h, frob_smul_left']
  ring

/-- **`frob` of a rank-one normal is the quadratic form**: `∑ᵢⱼ xᵢxⱼ Yᵢⱼ = xᵀ Y x`. -/
theorem frob_vecMulVec {n : ℕ} (x : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ) :
    frob (vecMulVec x x) Y = qfR Y x := by
  simp only [frob, qfR, dotProduct, Matrix.mulVec, vecMulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-! ## 2.  The zero-margin cut -/

/-- **A central cut of the widened relaxation.**  Rational normal, and the whole relaxation lies on
the closed side of the hyperplane through the rational centre `cX`: `0 ≤ frob (castQ normal)
(X - castQ cX)`.  This is `RelaxCut` with the margin erased — the form `RunData.hcut` asks for at
`del k := 0`, with `hcheck`/`hle`/`hrho` then reading `0 ≤ 0`. -/
structure ZeroCut {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) where
  normal : Matrix (Fin n) (Fin n) ℚ
  nonzero : normal ≠ 0
  separates : ∀ X : Matrix (Fin n) (Fin n) ℝ,
    relaxBodyLE A ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) X →
      0 ≤ frob (castQ normal) (X - castQ cX)

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}

/-- A vector with a zero entry at `j` (`SepOracle.delta`'s role, local copy). -/
def deltaQ {n : ℕ} (j : Fin n) : Fin n → ℚ := fun i => if i = j then 1 else 0

theorem qf_deltaQ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (j : Fin n) :
    QMCLeafB.EngineIterates.qf M (deltaQ j) = M j j := by
  simp [QMCLeafB.EngineIterates.qf, deltaQ, dotProduct, Matrix.mulVec]

/-- `signOf`, local copy (rational sign, `0` only at `0`). -/
def signOfQ (q : ℚ) : ℚ := if 0 < q then 1 else if q < 0 then -1 else 0

theorem signOfQ_cases (q : ℚ) : signOfQ q = 1 ∨ signOfQ q = -1 ∨ signOfQ q = 0 := by
  unfold signOfQ
  split_ifs <;> simp

theorem signOfQ_mul_self (q : ℚ) : signOfQ q * q = |q| := by
  unfold signOfQ
  by_cases h1 : 0 < q
  · rw [if_pos h1, one_mul, abs_of_pos h1]
  · rw [if_neg h1]
    by_cases h2 : q < 0
    · rw [if_pos h2, neg_mul, abs_of_neg h2]
      ring
    · have h0 : q = 0 := le_antisymm (le_of_not_gt h1) (le_of_not_gt h2)
      rw [if_neg h2, h0, mul_zero, abs_zero]

/-! ### 2.1  psd branch -/

/-- **psd branch**: a rational vector violating the relaxed quadratic form separates the relaxation
from the centre with margin zero (the rank-one normal `v vᵀ`). -/
def psdCut {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    {v : Fin n → ℚ}
    (h : QMCLeafB.EngineIterates.qf cX v < -(δ / 2) * (∑ i, v i ^ 2)) :
    ZeroCut A cX u δ where
  normal := vecMulVec v v
  nonzero := by
    intro h0
    have hv : v = 0 := by
      by_contra hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have hentry : (vecMulVec v v) i i = v i * v i := rfl
      have hzero : (vecMulVec v v) i i = 0 := by rw [h0]; simp
      rw [hentry] at hzero
      have hpos : 0 < v i * v i := mul_self_pos.mpr hi
      linarith
    subst hv
    have hz : QMCLeafB.EngineIterates.qf cX (0 : Fin n → ℚ) = 0 := by
      simp [QMCLeafB.EngineIterates.qf]
    have hs : (∑ i, (0 : Fin n → ℚ) i ^ 2) = 0 := by simp
    rw [hz, hs, mul_zero] at h
    exact lt_irrefl (0 : ℚ) h
  separates := by
    intro X hX
    obtain ⟨hpsd, -, -⟩ := hX
    set x : Fin n → ℝ := fun i => ((v i : ℚ) : ℝ) with hx
    have hb : -((((δ : ℚ) : ℝ)) / 2) * (∑ i, x i ^ 2) ≤ qfR X x := hpsd x
    have hcastvec : castQ (vecMulVec v v) = vecMulVec x x := by
      ext a b
      simp [castQ, hx, Matrix.vecMulVec_apply]
    have hqf : ((QMCLeafB.EngineIterates.qf cX v : ℚ) : ℝ) = qfR (castQ cX) x := by
      simp only [QMCLeafB.EngineIterates.qf, qfR, castQ, dotProduct, Matrix.mulVec, hx]
      push_cast
      ring
    have hrate : ((-(δ / 2) * (∑ i, v i ^ 2) : ℚ) : ℝ)
        = -((((δ : ℚ) : ℝ)) / 2) * (∑ i, x i ^ 2) := by
      simp only [hx]
      push_cast
      ring
    have hlt : qfR (castQ cX) x < -((((δ : ℚ) : ℝ)) / 2) * (∑ i, x i ^ 2) := by
      have h1 : ((QMCLeafB.EngineIterates.qf cX v : ℚ) : ℝ)
          < ((-(δ / 2) * (∑ i, v i ^ 2) : ℚ) : ℝ) := by
        exact_mod_cast h
      rwa [hqf, hrate] at h1
    rw [hcastvec, frob_sub', frob_vecMulVec, frob_vecMulVec]
    linarith

theorem psdBranch {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {cX : Matrix (Fin n) (Fin n) ℚ}
    {u δ : ℚ} {v : Fin n → ℚ}
    (h : QMCLeafB.EngineIterates.qf cX v < -(δ / 2) * (∑ i, v i ^ 2)) :
    Nonempty (ZeroCut A cX u δ) :=
  ⟨psdCut h⟩

/-! ### 2.2  diagonal branch -/

/-- The coordinate normal `sign(1 - cX_ii)·eᵢeᵢᵀ`. -/
def diagNormal {n : ℕ} (cX : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : Matrix (Fin n) (Fin n) ℚ :=
  signOfQ (1 - cX i i) • vecMulVec (deltaQ i) (deltaQ i)

/-- **Diagonal branch**: a diagonal entry off by more than `δ/4` separates the relaxation from the
centre with margin zero. -/
def diagCut {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (i : Fin n) (hδ : 0 ≤ δ) (h : δ / 4 < |cX i i - 1|) : ZeroCut A cX u δ where
  normal := diagNormal cX i
  nonzero := by
    have hcne : cX i i - 1 ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      linarith
    have hs : signOfQ (1 - cX i i) ≠ 0 := by
      intro hs0
      have h1 := signOfQ_mul_self (1 - cX i i)
      rw [hs0, zero_mul, abs_sub_comm] at h1
      have hpos : 0 < |cX i i - 1| := by
        have h4 : 0 ≤ δ / 4 := by linarith
        linarith
      rw [h1] at hpos
      exact lt_irrefl _ hpos
    intro h0
    have hz : diagNormal cX i = 0 := h0
    have hentry : (diagNormal cX i) i i = signOfQ (1 - cX i i) := by
      simp [diagNormal, deltaQ, Matrix.vecMulVec_apply]
    have hzero : (diagNormal cX i) i i = 0 := by rw [hz]; simp
    rw [hentry] at hzero
    exact hs hzero
  separates := by
    intro X hX
    obtain ⟨-, hdiag, -⟩ := hX
    set s : ℚ := signOfQ (1 - cX i i) with hsdef
    have hs : s = 1 ∨ s = -1 ∨ s = 0 := signOfQ_cases _
    have hsmul : s * (1 - cX i i) = |cX i i - 1| := by
      rw [hsdef, signOfQ_mul_self, abs_sub_comm]
    have hcastC : ((s : ℚ) : ℝ) * (1 - ((cX i i : ℚ) : ℝ)) = |((cX i i : ℚ) : ℝ) - 1| := by
      have h' := congrArg (fun q : ℚ => ((q : ℚ) : ℝ)) hsmul
      push_cast at h'
      exact h'
    have hstep : -|X i i - 1| ≤ ((s : ℚ) : ℝ) * (X i i - 1) := by
      rcases hs with h1 | h1 | h1
      · rw [h1]; push_cast; linarith [neg_abs_le (X i i - 1)]
      · rw [h1]; push_cast; linarith [le_abs_self (X i i - 1)]
      · rw [h1]; push_cast; linarith [abs_nonneg (X i i - 1)]
    have hXii : |X i i - 1| ≤ (((δ : ℚ)) : ℝ) / 4 := hdiag i
    have hR : (((δ : ℚ)) : ℝ) / 4 < |((cX i i : ℚ) : ℝ) - 1| := by
      have hc : ((δ / 4 : ℚ) : ℝ) < ((|cX i i - 1| : ℚ) : ℝ) := by exact_mod_cast h
      have h3 : ((|cX i i - 1| : ℚ) : ℝ) = |((cX i i : ℚ) : ℝ) - 1| := by push_cast; ring
      calc (((δ : ℚ)) : ℝ) / 4 = ((δ / 4 : ℚ) : ℝ) := by push_cast; ring
        _ < ((|cX i i - 1| : ℚ) : ℝ) := hc
        _ = |((cX i i : ℚ) : ℝ) - 1| := h3
    have hsingle : (fun j => ((deltaQ i j : ℚ) : ℝ)) = Pi.single i (1 : ℝ) := by
      funext j
      simp only [deltaQ, Pi.single_apply]
      by_cases h : j = i <;> simp [h]
    have hcastN0 : castQ (vecMulVec (deltaQ i) (deltaQ i))
        = vecMulVec (fun j => ((deltaQ i j : ℚ) : ℝ)) (fun j => ((deltaQ i j : ℚ) : ℝ)) := by
      ext a b
      simp only [castQ, Matrix.vecMulVec_apply, Matrix.of_apply]
      push_cast
      ring
    have hcastN : castQ (vecMulVec (deltaQ i) (deltaQ i))
        = vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
      rw [hcastN0, hsingle]
    have hcast_smul : castQ (signOfQ (1 - cX i i) • vecMulVec (deltaQ i) (deltaQ i))
        = ((signOfQ (1 - cX i i) : ℚ) : ℝ) • castQ (vecMulVec (deltaQ i) (deltaQ i)) := by
      ext a b
      simp only [castQ, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    have hcast : castQ (diagNormal cX i)
        = ((s : ℚ) : ℝ) • vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
      show castQ (signOfQ (1 - cX i i) • vecMulVec (deltaQ i) (deltaQ i)) = _
      rw [hcast_smul, hcastN, hsdef]
    have hN1 : frob (vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ))) X = X i i := by
      rw [frob_vecMulVec]
      simp [qfR, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ]
    have hN2 : frob (vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ))) (castQ cX)
        = ((cX i i : ℚ) : ℝ) := by
      rw [frob_vecMulVec]
      simp [qfR, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, castQ]
    rw [hcast, frob_sub', frob_smul_left', frob_smul_left', hN1, hN2]
    nlinarith [hstep, hXii, hR, hcastC]

theorem diagBranch {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {cX : Matrix (Fin n) (Fin n) ℚ}
    {u δ : ℚ} (i : Fin n) (hδ : 0 ≤ δ) (h : δ / 4 < |cX i i - 1|) :
    Nonempty (ZeroCut A cX u δ) :=
  ⟨diagCut i hδ h⟩

/-! ### 2.3  trace branch (high side) -/

/-- **Trace branch, high side**: the centre is above the relaxation's trace bound.  The normal is
the rational weight matrix `Aq` (whose cast is the real `A`), negated.  `hA0` is what `RunData.hcne`
needs; for the campaign's `A = wMatrix G` it is `wMatrix_ne_zero`. -/
def traceCut {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (Aq : Matrix (Fin n) (Fin n) ℚ)
    (cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ)
    (hA : castQ Aq = A) (hA0 : A ≠ 0) (h : u + δ / 2 < frob A (castQ cX)) :
    ZeroCut A cX u δ where
  normal := -Aq
  nonzero := by
    intro h0
    apply hA0
    have hnegq : castQ (-Aq) = -castQ Aq := by
      ext a b
      simp [castQ]
    have h1 : castQ (-Aq) = castQ (0 : Matrix (Fin n) (Fin n) ℚ) := by rw [h0]
    have h2 : castQ (0 : Matrix (Fin n) (Fin n) ℚ) = 0 := by
      ext a b
      simp [castQ]
    rw [hnegq, hA, h2] at h1
    exact neg_eq_zero.mp h1
  separates := by
    intro X hX
    obtain ⟨-, -, htr⟩ := hX
    have hR : ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 < frob A (castQ cX) := h
    have hneg : castQ (-Aq) = -A := by
      rw [← hA]
      ext a b
      simp [castQ]
    rw [hneg, frob_neg_left', frob_sub']
    linarith

/-! ## 3.  The flat form `RunData.hcut` speaks -/

theorem frob_flat_dot' {n : ℕ} (N Y : Matrix (Fin n) (Fin n) ℝ) :
    frob N Y = ∑ k : Fin (n * n),
      QMCLeafB.AnswerProducer.flat N k * QMCLeafB.AnswerProducer.flat Y k := by
  calc frob N Y = ∑ i, ∑ j, N i j * Y i j := rfl
    _ = ∑ p : Fin n × Fin n, N p.1 p.2 * Y p.1 p.2 :=
        (Fintype.sum_prod_type (f := fun p : Fin n × Fin n => N p.1 p.2 * Y p.1 p.2)).symm
    _ = ∑ k : Fin (n * n),
          QMCLeafB.AnswerProducer.flat N k * QMCLeafB.AnswerProducer.flat Y k := by
        rw [← Equiv.sum_comp finProdFinEquiv
          (fun k : Fin (n * n) =>
            QMCLeafB.AnswerProducer.flat N k * QMCLeafB.AnswerProducer.flat Y k)]
        exact Finset.sum_congr rfl (fun p _ => by simp [QMCLeafB.AnswerProducer.flat])

/-- **`RunData.hcut` at `del = 0`.**  On the campaign's `Boundary.relaxBall`, a central cut gives
`0 ≤ normal ⬝ᵥ (z - centre)` in the loop's own flat coordinates. -/
theorem ZeroCut.separates_flat {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} (C : ZeroCut A cX u δ) (M : ℝ) :
    ∀ z : Fin (n * n) → ℝ,
      z ∈ QMCLeafB.Boundary.relaxBall A ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) M →
      0 ≤ (fun k : Fin (n * n) => ((flatQ C.normal k : ℚ) : ℝ)) ⬝ᵥ
            (z - QMCLeafB.AnswerProducer.flat (castQ cX)) := by
  intro z hz
  have hzbody : QMCLeafB.BallFloor.relaxBodyLE A ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ)
      (QMCLeafB.Boundary.unflat z) := hz.1
  have h := C.separates (QMCLeafB.Boundary.unflat z) hzbody
  rw [frob_flat_dot'] at h
  have h2 : (QMCLeafB.AnswerProducer.flat (QMCLeafB.Boundary.unflat z - castQ cX))
      = z - QMCLeafB.AnswerProducer.flat (castQ cX) := by
    rw [QMCLeafB.Boundary.flat_sub, QMCLeafB.Boundary.flat_unflat]
  rw [h2] at h
  have h3 : (∑ k : Fin (n * n), QMCLeafB.AnswerProducer.flat (castQ C.normal) k
        * (z - QMCLeafB.AnswerProducer.flat (castQ cX)) k)
      = ∑ k : Fin (n * n), (((flatQ C.normal k : ℚ)) : ℝ)
        * (z - QMCLeafB.AnswerProducer.flat (castQ cX)) k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [flatQ, castQ, QMCLeafB.AnswerProducer.flat]
  rw [h3] at h
  rwa [dotProduct]

end QMCLeafB.VerdictCut

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.VerdictCut.flatQ_ne_zero
#print axioms QMCLeafB.VerdictCut.frob_vecMulVec
#print axioms QMCLeafB.VerdictCut.psdCut
#print axioms QMCLeafB.VerdictCut.diagCut
#print axioms QMCLeafB.VerdictCut.traceCut
#print axioms QMCLeafB.VerdictCut.ZeroCut.separates_flat
#print axioms QMCLeafB.VerdictCut.frob_flat_dot'


