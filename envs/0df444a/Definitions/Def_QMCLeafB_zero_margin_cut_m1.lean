-- Prove2me | Definitions.Def_QMCLeafB_zero_margin_cut_m1
-- name    : QMCLeafB_zero_margin_cut_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:12:09.277758+00:00
-- url     : https://prove2.me/theorems/5fdbdb28-e091-4143-81c7-eaea2535e3d4
-- title:
--   QMCLeafB zero_margin_cut_m1
-- statement:
--   # leaf B phase 13 — `zero-margin-cut` (swarm `smw17fqzz`, member m1, direction d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_relax_oracle_m4
/-
# leaf B phase 13 — `zero-margin-cut` (swarm `smw17fqzz`, member m1, direction d6)

`QMCLeafB.VerdictSound.RunData` couples the recorded cut margin and the recorded depth:

    hcheck : (del k)^2 ≤ ((cd k).rho)^2 * sigmaQ (cd k).c (cd k).p

so a *positive* margin forces a *positive* depth `rho`, and the shelf's only explicit halving
lemma — `SimLoop.halving_time_explicit`, `4N` rounds at depth **zero** — is stated at `rho = 0`.
There is no ceiling lemma on the shelf at a positive depth (proved here separately, in
`Check_shallow_ceiling_m1`, at the shallow ceiling `1/(8N)`), and, worse, a positive `rho` must be
justified against the recorded cut anyway.  The clean resolution — and the one the campaign's
`central_run_budget` (`Aat_vol_below_central`) is built for — is the **central cut**:
`rho = 0`, `del = 0`, `rmax = 0`, `m = 4(n·n)`.

What makes that resolvable is that the relaxed separation oracle's three *used* branches prove more
than `RelaxCut` exposes.  `RelaxCut.separates` says `-margin ≤ normal ⬝ (X - cX)`; the actual
arguments (`psdCutOf`, `diagCutOf`, `traceHighCutOf`) give

    0 ≤ normal ⬝ (X - cX)

outright — the relaxation lies on the *closed* side of the hyperplane through the centre.  That is
all `RunData` needs: `hcut` reads `-del ≤ …`, so `del := 0` is legitimate, and then `hcheck` with
`rho := 0` is `0 ≤ 0`.

Contents:

* `Cut0` — a zero-margin cut: rational normal plus the separation `0 ≤ normal ⬝ (X - cX)` over the
  relaxation;
* `psdCut0`, `diagCut0`, `traceHighCut0` — the three branches, re-proved at margin zero (the
  `traceLowCutOf` branch is deliberately excluded: the centre satisfies the trace bound there, so it
  does not separate and the loop never uses it — `relaxMem_or_cut` picks `RelaxMem` instead);
* `psdBranch0`, `diagBranch0`, `traceHighBranch0`, and the totality
  `relaxMem_or_cut0 : RelaxMem A cX u δ ∨ Nonempty (Cut0 A cX u δ)`;
* `Cut0.normal_ne_zero` for each branch — `RunData.hcne`;
* `Cut0.separates_ball0` — the flat shape `RunData.hcut` speaks, on `Boundary.relaxBall`, with the
  margin read as `0`; and `Cut0.separates_hcutδ0`, pinned to `simulate_refuted_sound`'s `hcutδ` at
  `t - εr`.

No `sorry`, no `axiom`; audits at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.ZeroMarginCut

open QMCLeafB.RelaxOracle
open QMCLeafB.SepOracle

variable {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}

/-! ## 1.  The zero-margin cut -/

/-- **A central cut.**  Rational normal and the separation of the *whole* relaxation from the
hyperplane **through the centre**: `0 ≤ normal ⬝ (X - cX)`.  This is `RelaxCut` with the margin
erased, which is exactly what the loop stores when it records `del = 0`, `rho = 0`. -/
structure Cut0 (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) where
  /-- the cut normal, row-major flat in the loop's own coordinates -/
  normal : Matrix (Fin n) (Fin n) ℚ
  /-- the relaxation lies on the closed side of the hyperplane through the centre -/
  separates : ∀ X : Matrix (Fin n) (Fin n) ℝ,
    QMCLeafB.BallFloor.relaxBodyLE (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) X →
      0 ≤ frob (castMat normal) (X - castMat cX)

/-! ## 2.  The three used branches, at margin zero -/

/-- **psd branch** (`Cut0` form): a violated relaxed quadratic form separates the relaxation from
the centre with margin zero. -/
def psdCut0 {v : Fin n → ℚ} (h : qf cX v < -(δ / 2) * (∑ i, v i ^ 2)) : Cut0 A cX u δ where
  normal := vecMulVec v v
  separates := by
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
    linarith

/-- **Diagonal branch** (`Cut0` form): a diagonal entry off by more than `δ/4` separates the
relaxation from the centre with margin zero. -/
def diagCut0 (i : Fin n) (h : δ / 4 < |cX i i - 1|) : Cut0 A cX u δ where
  normal := diagNormal cX i
  separates := by
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
    linarith

/-- **Trace branch, high side** (`Cut0` form): the centre is above the relaxation's trace bound. -/
def traceHighCut0 (h : u + δ / 2 < frob A cX) : Cut0 A cX u δ where
  normal := -A
  separates := by
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
    linarith

/-! ## 3.  Totality at margin zero -/

theorem psdBranch0 {v : Fin n → ℚ} (h : qf cX v < -(δ / 2) * (∑ i, v i ^ 2)) :
    Nonempty (Cut0 A cX u δ) :=
  ⟨psdCut0 h⟩

theorem diagBranch0 (i : Fin n) (h : δ / 4 < |cX i i - 1|) : Nonempty (Cut0 A cX u δ) :=
  ⟨diagCut0 i h⟩

theorem traceHighBranch0 (h : u + δ / 2 < frob A cX) : Nonempty (Cut0 A cX u δ) :=
  ⟨traceHighCut0 h⟩

/-- **The relaxed oracle is total at margin zero.**  Every rational centre is either inside the
relaxation (`RelaxMem`, the loop's `ok`) or separated from it by a rational normal *through the
centre* — no margin.  The `traceLowCutOf` side of `relaxMem_or_cut` is not used, exactly as in the
relaxed oracle: there the centre itself satisfies the trace bound, so it cannot be separated. -/
theorem relaxMem_or_cut0 (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (u δ : ℚ) (hδ : 0 < δ) :
    RelaxMem A cX u δ ∨ Nonempty (Cut0 A cX u δ) := by
  by_cases htr : frob A cX ≤ u + δ / 2
  · by_cases hdiag : ∀ i, |cX i i - 1| ≤ δ / 4
    · by_cases hpsd : ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qf cX x
      · exact Or.inl ⟨hδ, hpsd, hdiag, htr⟩
      · obtain ⟨v, hv⟩ := not_forall.mp hpsd
        exact Or.inr (psdBranch0 (lt_of_not_ge hv))
    · obtain ⟨i, hi⟩ := not_forall.mp hdiag
      exact Or.inr (diagBranch0 i (lt_of_not_ge hi))
  · exact Or.inr ⟨traceHighCut0 (lt_of_not_ge htr)⟩

/-! ## 4.  Non-zero normals (`RunData.hcne`) -/

theorem psdCut0_normal_ne_zero {v : Fin n → ℚ} (h : qf cX v < -(δ / 2) * (∑ i, v i ^ 2)) :
    (psdCut0 (A := A) (cX := cX) (u := u) (δ := δ) h).normal ≠ 0 := by
  intro h0
  have hv : v = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hentry : (vecMulVec v v) i i = v i * v i := Matrix.vecMulVec_apply v v i i
    have hzero : (vecMulVec v v) i i = 0 := by
      have hz : (vecMulVec v v) = 0 := h0
      rw [hz]
      simp
    rw [hentry] at hzero
    have hpos : 0 < v i * v i := mul_self_pos.mpr hi
    linarith
  subst hv
  have hz : qf cX (0 : Fin n → ℚ) = 0 := by simp [qf]
  have hs : (∑ i, (0 : Fin n → ℚ) i ^ 2) = 0 := by simp
  rw [hz, hs, mul_zero] at h
  exact lt_irrefl (0 : ℚ) h

theorem diagCut0_normal_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {cX : Matrix (Fin n) (Fin n) ℚ}
    {u δ : ℚ} (i : Fin n) (hδ : 0 ≤ δ) (h : δ / 4 < |cX i i - 1|) :
    (diagCut0 (A := A) (cX := cX) (u := u) (δ := δ) i h).normal ≠ 0 := by
  have habs : 0 < |cX i i - 1| := by
    have h4 : 0 ≤ δ / 4 := by linarith
    linarith
  have hs : signOf (1 - cX i i) ≠ 0 := by
    intro hs0
    have h1 := signOf_mul_self (1 - cX i i)
    rw [hs0, zero_mul, abs_sub_comm] at h1
    rw [h1] at habs
    exact lt_irrefl _ habs
  intro h0
  have hentry : (diagNormal cX i) i i = signOf (1 - cX i i) := by
    simp [diagNormal, delta, Matrix.vecMulVec_apply]
  have hzero : (diagNormal cX i) i i = 0 := by
    have hz : diagNormal cX i = 0 := h0
    rw [hz]
    simp
  rw [hentry] at hzero
  exact hs hzero

theorem traceHighCut0_normal_ne_zero {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hA : A ≠ 0) (h : u + δ / 2 < frob A cX) :
    (traceHighCut0 (A := A) (cX := cX) (u := u) (δ := δ) h).normal ≠ 0 := by
  intro h0
  apply hA
  have hthis : (traceHighCut0 (A := A) (cX := cX) (u := u) (δ := δ) h).normal = -A := rfl
  rw [hthis] at h0
  exact neg_eq_zero.mp h0

/-! ## 5.  The shape `RunData.hcut` speaks -/


/-- **The flat form** (the loop's own coordinates): for a flat point whose unflattening lies in the
relaxation, `0 ≤ normal ⬝ᵥ (z - centre)`.  With `del k := 0` this is `RunData.hcut` verbatim. -/
theorem Cut0.separates_flat (C : Cut0 A cX u δ) :
    ∀ z : Fin (n * n) → ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) (QMCLeafB.Boundary.unflat z) →
      0 ≤ (fun k : Fin (n * n) => ((flatQ C.normal k : ℚ) : ℝ)) ⬝ᵥ
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

/-- The same on `Boundary.relaxBall` — the set `RunData.hcut` quantifies over. -/
theorem Cut0.separates_ball (C : Cut0 A cX u δ) (M : ℝ) :
    ∀ z : Fin (n * n) → ℝ,
      z ∈ QMCLeafB.Boundary.relaxBall (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) M →
      0 ≤ (fun k : Fin (n * n) => ((flatQ C.normal k : ℚ) : ℝ)) ⬝ᵥ
            (z - QMCLeafB.AnswerProducer.flat (castMat cX)) :=
  fun z hz => C.separates_flat z hz.1

/-- **Pinned to `hcutδ` at zero margin.**  A zero-margin cut of the relaxation at tolerance `δq`
is `simulate_refuted_sound`'s `hcutδ` hypothesis at `δ k := 0`, `u = t - εr`. -/
theorem Cut0.separates_hcutδ {t εr : ℚ} (C : Cut0 A cX (t - εr) δ) (M : ℝ) :
    ∀ z : Fin (n * n) → ℝ,
      z ∈ QMCLeafB.Boundary.relaxBall (castMat A) (((t : ℚ) : ℝ) - ((εr : ℚ) : ℝ))
        ((δ : ℚ) : ℝ) M →
      -((0 : ℚ) : ℝ) ≤ (fun k : Fin (n * n) => ((flatQ C.normal k : ℚ) : ℝ)) ⬝ᵥ
            (z - QMCLeafB.AnswerProducer.flat (castMat cX)) := by
  have hcast : (((t - εr : ℚ)) : ℝ) = ((t : ℚ) : ℝ) - ((εr : ℚ) : ℝ) := by push_cast; ring
  intro z hz
  have hz' : z ∈ QMCLeafB.Boundary.relaxBall (castMat A) (((t - εr : ℚ)) : ℝ)
      ((δ : ℚ) : ℝ) M := by
    rw [hcast]
    exact hz
  simpa using C.separates_ball M z hz'

end QMCLeafB.ZeroMarginCut

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.ZeroMarginCut.psdCut0
#print axioms QMCLeafB.ZeroMarginCut.diagCut0
#print axioms QMCLeafB.ZeroMarginCut.traceHighCut0
#print axioms QMCLeafB.ZeroMarginCut.relaxMem_or_cut0
#print axioms QMCLeafB.ZeroMarginCut.psdCut0_normal_ne_zero
#print axioms QMCLeafB.ZeroMarginCut.diagCut0_normal_ne_zero
#print axioms QMCLeafB.ZeroMarginCut.traceHighCut0_normal_ne_zero
#print axioms QMCLeafB.ZeroMarginCut.Cut0.separates_ball
#print axioms QMCLeafB.ZeroMarginCut.Cut0.separates_hcutδ


