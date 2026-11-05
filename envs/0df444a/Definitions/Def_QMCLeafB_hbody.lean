-- Prove2me | Definitions.Def_QMCLeafB_hbody
-- name    : QMCLeafB_hbody
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:27:12.651211+00:00
-- url     : https://prove2.me/theorems/96f25237-51dd-4fb6-bafe-ae8384c22b65
-- title:
--   QMCLeafB hbody
-- statement:
--   # leaf B phase 23 — the `hbody` slot at the open stratum, from genuine separation
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_audit2
/-
# leaf B phase 23 — the `hbody` slot at the open stratum, from genuine separation
(swarm `smw1qbrnt`, member m6, direction d7 `threshold-separator`)

The one open stratum of the campaign (audit2 §5, `anchor3_*`) is: interior `(G, t)` with a
**nonempty** real relaxed body but **no pinched member** — the exemplar `(G₁, t₁)`.  At such a
point `ok ≡ false` below the horizon, so the `RunParts` producer runs on its `false` branch, and
every slot of the producer's geometric ledger is free *except* `RunPartsDilate.dilCut`'s

    hbody : ∀ k, ok k = false → ∀ X, relaxBodyLE (castMat A) u δ X →
              -0 ≤ frob (castMat dM) (X - castMat (cX k))

a single nonzero rational direction `dM` that supports the whole real relaxation at the recorded
centre.  The settled land says the trace ceiling is exact and not widenable (`Check_ceiling_m3`)
and that `CoreDataG` is dead at every false-bit point (`Check_crater_m2`); but `hbody` itself was
never produced at a positive-margin-free (non-member) centre.  This file produces it.

## What is proved

* §1 **The stratum is a threshold.**  `relaxBodyLE` is monotone in the level `u`
  (`relaxBodyLE_mono`), so `RelaxMem` is *upward* closed in `u` (`relaxMem_mono`) and
  non-membership is *downward* closed (`not_relaxMem_mono`); emptiness likewise
  (`body_empty_mono`).
* §2 **Separation at a non-member.**  `separator_of_not_mem`: at a rational centre `cX` that is
  not a `RelaxMem` member (with `0 < δ`, `0 < n`), there is an **explicit rational** `dM ≠ 0` with
  `-0 ≤ frob (castMat dM) (X - castMat cX)` for every *real* point `X` of the relaxation.  The
  three branches are the relaxed oracle's own (`psdCutOf` / `diagCutOf` / `traceHighCutOf`) read at
  margin `0`; the only new work is the non-vanishing of the normal in each branch — the `A = 0` and
  `cX_ii = 1` degeneracies are killed by non-emptiness of the body.
* §3 **One separator serves the whole level interval** (`separator_below`): if `cX` is not a member
  at `u₁`, the *same* `dM` supports the relaxation at **every** `u ≤ u₁`.
* §4 **The `hbody` slot.**  `hbody_frozen_window` gives the `∀ k`-shaped `hbody` at a frozen
  recorded centre; `anchor3_separator` / `anchor3_separator_below` instantiate at `(G₁, t₁)` from
  `Check_emptybody_m5.no_pinched_member_G₁`.
* §5 **What is left, named.**  `FrozenDrift` is the residual `hdriftd` at the frozen window.  It is
  not proved here.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`⊊` is never used; every block comment is closed properly.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QMCLeafB.HBodyM6

open QMCLeafB.SepOracle
open QMCLeafB.BallFloor (relaxBodyLE)
open QMCLeafB.RelaxOracle

/-! ## 1.  The stratum is a threshold: monotonicity in the relaxation level -/

/-- `relaxBodyLE` is monotone in the level `u`: raising the level only relaxes the objective
conjunct, so the body only grows. -/
theorem relaxBodyLE_mono {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ} {u₁ u₂ : ℝ}
    (h : u₁ ≤ u₂) {X : Matrix (Fin n) (Fin n) ℝ} (hX : relaxBodyLE A u₁ δ X) :
    relaxBodyLE A u₂ δ X := by
  obtain ⟨hpsd, hdiag, htr⟩ := hX
  exact ⟨hpsd, hdiag, le_trans htr (by linarith)⟩

/-- The membership verdict is **upward** closed in the level. -/
theorem relaxMem_mono {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ} {u₁ u₂ : ℚ}
    (h : u₁ ≤ u₂) (hM : RelaxMem A cX u₁ δ) : RelaxMem A cX u₂ δ := by
  obtain ⟨hδ, hpsd, hdiag, htr⟩ := hM
  exact ⟨hδ, hpsd, hdiag, le_trans htr (by linarith)⟩

/-- Non-membership is **downward** closed in the level. -/
theorem not_relaxMem_mono {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ} {u₁ u₂ : ℚ}
    (h : u₁ ≤ u₂) (hM : ¬ RelaxMem A cX u₂ δ) : ¬ RelaxMem A cX u₁ δ := by
  intro h1
  exact hM (relaxMem_mono h h1)

/-- Emptiness of the real body is **downward** closed in the level. -/
theorem body_empty_mono {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ} {u₁ u₂ : ℝ}
    (h : u₂ ≤ u₁) (hE : ∀ X : Matrix (Fin n) (Fin n) ℝ, ¬ relaxBodyLE A u₁ δ X) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ, ¬ relaxBodyLE A u₂ δ X := by
  intro X hX
  exact hE X (relaxBodyLE_mono h hX)

/-! ## 2.  Separation at a non-member: an explicit rational direction -/

/-- The identity matrix is nonzero as soon as `n > 0`. -/
theorem oneMat_ne_zero {n : ℕ} (hn : 0 < n) :
    (1 : Matrix (Fin n) (Fin n) ℚ) ≠ 0 := by
  intro h
  have h' := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
  have h'' : (1 : ℚ) = 0 := by simpa using h'
  exact one_ne_zero h''

/-- `signOf` of a nonzero rational is nonzero. -/
theorem signOf_ne_zero {q : ℚ} (hq : q ≠ 0) : signOf q ≠ 0 := by
  intro h
  have h1 : signOf q * q = |q| := signOf_mul_self q
  rw [h, zero_mul] at h1
  exact hq (abs_eq_zero.mp h1.symm)

/-- The rank-one matrix `v vᵀ` is nonzero for `v ≠ 0`. -/
theorem vecMulVec_self_ne_zero {n : ℕ} {v : Fin n → ℚ} (hv : v ≠ 0) :
    vecMulVec v v ≠ 0 := by
  intro h
  apply hv
  funext j
  have h' := congrFun (congrFun h j) j
  simp only [Matrix.vecMulVec_apply, Matrix.zero_apply] at h'
  exact (mul_eq_zero.mp h').elim id id

/-- The pairing of the zero matrix with anything vanishes. -/
theorem frob_zero_left {K : Type*} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) :
    frob (0 : Matrix (Fin n) (Fin n) K) X = 0 := by
  simp [frob]

/-- **Separation at a non-member centre.**  If the rational centre `cX` is not a `RelaxMem`
member at level `u`, then some nonzero rational direction supports the whole real relaxation at
`cX`: `0 ≤ ⟪dM, X - cX⟫` for every real member `X`.  This is the `hbody` obligation of
`RunPartsDilate.dilCut` at a single (frozen) centre, with margin exactly `0`. -/
theorem separator_of_not_mem {n : ℕ} (hn : 0 < n)
    (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ)
    (h : ¬ RelaxMem A cX u δ) :
    ∃ dM : Matrix (Fin n) (Fin n) ℚ, dM ≠ 0 ∧
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        relaxBodyLE (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) X →
        -(((0 : ℚ)) : ℝ) ≤ frob (castMat dM) (X - castMat cX) := by
  classical
  by_cases hempty : ∃ X : Matrix (Fin n) (Fin n) ℝ,
      relaxBodyLE (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) X
  · obtain ⟨X₀, hX₀⟩ := hempty
    by_cases htr : frob A cX ≤ u + δ / 2
    · by_cases hdiag : ∀ i, |cX i i - 1| ≤ δ / 4
      · by_cases hpsd : ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qf cX x
        · exact absurd ⟨hδ, hpsd, hdiag, htr⟩ h
        · -- psd branch: the rank-one direction `v vᵀ`
          push_neg at hpsd
          obtain ⟨v, hv⟩ := hpsd
          have hq0 : qf cX (0 : Fin n → ℚ) = 0 := by simp [QMCLeafB.SepOracle.qf]
          have hv0 : v ≠ 0 := by
            intro h0
            rw [h0, hq0] at hv
            simp at hv
          refine ⟨vecMulVec v v, vecMulVec_self_ne_zero hv0, fun X hX => ?_⟩
          obtain ⟨hpsdX, -, -⟩ := hX
          have hcast : qf (castMat cX) (fun i => ((v i : ℚ) : ℝ)) = ((qf cX v : ℚ) : ℝ) := by
            simpa [castMat] using qf_map (Rat.castHom ℝ) cX v
          have hb : -((((δ : ℚ) : ℝ)) / 2) * (∑ i, ((v i : ℚ) : ℝ) ^ 2)
              ≤ qf X (fun i => ((v i : ℚ) : ℝ)) := by
            simpa only [QMCLeafB.BallFloor.qfR, QMCLeafB.SepOracle.qf]
              using hpsdX (fun i => ((v i : ℚ) : ℝ))
          have hc : ((qf cX v : ℚ) : ℝ)
              < -((((δ : ℚ) : ℝ)) / 2) * (∑ i, ((v i : ℚ) : ℝ) ^ 2) := by
            have h1 : ((qf cX v : ℚ) : ℝ) < ((-(δ / 2) * (∑ i, v i ^ 2) : ℚ) : ℝ) := by
              exact_mod_cast hv
            have h2 : ((-(δ / 2) * (∑ i, v i ^ 2) : ℚ) : ℝ)
                = -((((δ : ℚ) : ℝ)) / 2) * (∑ i, ((v i : ℚ) : ℝ) ^ 2) := by
              push_cast
              ring
            rwa [h2] at h1
          have hkey : frob (castMat (vecMulVec v v)) (X - castMat cX)
              = qf X (fun i => ((v i : ℚ) : ℝ)) - ((qf cX v : ℚ) : ℝ) := by
            rw [castMat_vecMulVec, frob_sub, ← qf_eq_frob X (fun i => ((v i : ℚ) : ℝ)),
              ← qf_eq_frob (castMat cX) (fun i => ((v i : ℚ) : ℝ)), hcast]
          rw [hkey]
          simp only [Rat.cast_zero, neg_zero]
          linarith
      · -- diagonal branch: the coordinate direction `sign(1 - cX_ii) · e_i e_iᵀ`
        push_neg at hdiag
        obtain ⟨i, hi⟩ := hdiag
        have hci : cX i i ≠ 1 := by
          intro h1
          rw [h1] at hi
          simp at hi
          linarith
        have hsign : signOf (1 - cX i i) ≠ 0 :=
          signOf_ne_zero (by intro h1; exact hci (by linarith))
        have hvv : vecMulVec (delta (K := ℚ) i) (delta (K := ℚ) i) i i = 1 := by
          simp [Matrix.vecMulVec_apply, delta]
        have hnn : diagNormal cX i i i = signOf (1 - cX i i) := by
          simp only [diagNormal, Matrix.smul_apply, smul_eq_mul, hvv, mul_one]
        have hnz : diagNormal cX i ≠ 0 := by
          intro h0
          have h1 := congrFun (congrFun h0 i) i
          rw [Matrix.zero_apply, hnn] at h1
          exact hsign h1
        refine ⟨diagNormal cX i, hnz, fun X hX => ?_⟩
        obtain ⟨-, hdiagX, -⟩ := hX
        have hs : signOf (1 - cX i i) = 1 ∨ signOf (1 - cX i i) = -1
            ∨ signOf (1 - cX i i) = 0 := signOf_cases _
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
        have hXii : |X i i - 1| ≤ (((δ : ℚ)) : ℝ) / 4 := hdiagX i
        have hR : (((δ : ℚ)) : ℝ) / 4 < |((cX i i : ℚ) : ℝ) - 1| := by
          have h1 : (((δ / 4 : ℚ)) : ℝ) < ((|cX i i - 1| : ℚ) : ℝ) := by exact_mod_cast hi
          have h2 : (((δ : ℚ)) : ℝ) / 4 = ((δ / 4 : ℚ) : ℝ) := by push_cast; ring
          have h3 : ((|cX i i - 1| : ℚ) : ℝ) = |((cX i i : ℚ) : ℝ) - 1| := by push_cast; ring
          rw [h2, ← h3]
          exact h1
        have hkey : frob (castMat (diagNormal cX i)) (X - castMat cX)
            = (((signOf (1 - cX i i) : ℚ)) : ℝ) * (X i i - 1)
              + (((signOf (1 - cX i i) : ℚ)) : ℝ) * (1 - ((cX i i : ℚ) : ℝ)) := by
          rw [frob_sub, frob_diagNormal i X, frob_diagNormal i (castMat cX)]
          have hcc : castMat cX i i = ((cX i i : ℚ) : ℝ) := rfl
          rw [hcc]
          ring
        rw [hkey, hcastC]
        simp only [Rat.cast_zero, neg_zero]
        push_cast
        linarith
    · -- trace branch: the centre sits above the relaxation's objective bound
      push_neg at htr
      have hA : A ≠ 0 := by
        intro h0
        have hz : frob A cX = 0 := by rw [h0]; exact frob_zero_left cX
        have hlt : u + δ / 2 < 0 := by
          have h' := htr
          rw [hz] at h'
          exact h'
        have hltR : ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 < 0 := by
          have h' : (((u + δ / 2 : ℚ)) : ℝ) < 0 := by exact_mod_cast hlt
          have h2 : (((u + δ / 2 : ℚ)) : ℝ) = ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 := by
            push_cast
            ring
          rwa [h2] at h'
        have hcast : castMat A = 0 := by rw [h0]; simp [castMat]
        obtain ⟨-, -, htrX⟩ := hX₀
        have hcastA : frob (castMat A) X₀
            ≤ ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 := htrX
        rw [hcast, frob_zero_left] at hcastA
        linarith
      have hneg : (-A : Matrix (Fin n) (Fin n) ℚ) ≠ 0 := neg_ne_zero.mpr hA
      refine ⟨-A, hneg, fun X hX => ?_⟩
      obtain ⟨-, -, htrX⟩ := hX
      have hR : ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 < ((frob A cX : ℚ) : ℝ) := by
        have h1 : ((u + δ / 2 : ℚ) : ℝ) < ((frob A cX : ℚ) : ℝ) := by exact_mod_cast htr
        have h2 : ((u + δ / 2 : ℚ) : ℝ) = ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 := by
          push_cast
          ring
        rwa [h2] at h1
      have hcastA : frob (castMat A) X ≤ ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 := htrX
      have hcastc : frob (castMat A) (castMat cX) = ((frob A cX : ℚ) : ℝ) :=
        frob_map (Rat.castHom ℝ) A cX
      have hnegM : castMat (-A) = -castMat A := by
        ext a b
        simp [castMat]
      have hkey : frob (castMat (-A)) (X - castMat cX)
          = -(frob (castMat A) X - frob (castMat A) (castMat cX)) := by
        rw [hnegM, frob_neg_left, frob_sub]
      rw [hkey, hcastc]
      simp only [Rat.cast_zero, neg_zero]
      push_cast
      linarith
  · -- empty body: any nonzero direction works
    push_neg at hempty
    refine ⟨1, oneMat_ne_zero hn, fun X hX => ?_⟩
    exact absurd hX (hempty X)

/-! ## 3.  One separator serves the whole level interval below the membership threshold -/

/-- **The threshold form.**  If `cX` is not a member at `u₁`, then a *single* nonzero rational
direction supports the relaxation at `cX` at **every** level `u ≤ u₁`. -/
theorem separator_below {n : ℕ} (hn : 0 < n)
    (A cX : Matrix (Fin n) (Fin n) ℚ) (u₁ δ : ℚ) (hδ : 0 < δ)
    (h : ¬ RelaxMem A cX u₁ δ) :
    ∃ dM : Matrix (Fin n) (Fin n) ℚ, dM ≠ 0 ∧
      ∀ u : ℚ, u ≤ u₁ → ∀ X : Matrix (Fin n) (Fin n) ℝ,
        relaxBodyLE (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) X →
        -(((0 : ℚ)) : ℝ) ≤ frob (castMat dM) (X - castMat cX) := by
  obtain ⟨dM, hne, hsep⟩ := separator_of_not_mem hn A cX u₁ δ hδ h
  refine ⟨dM, hne, fun u hu X hX => hsep X ?_⟩
  exact relaxBodyLE_mono (by exact_mod_cast hu) hX

/-! ## 4.  The `hbody` slot of `dilCut` at a frozen recorded centre -/

/-- **The `∀ k`-shaped `hbody` at a frozen centre.**  `dilCut`'s `hbody` field is indexed by the
round; with the recorded centre frozen at one non-member `cXp` it is the same inequality at every
`k`, so §2 discharges it verbatim. -/
theorem hbody_frozen_window {n : ℕ} (hn : 0 < n)
    (A cXp : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ)
    (h : ¬ RelaxMem A cXp u δ) :
    ∃ dM : Matrix (Fin n) (Fin n) ℚ, dM ≠ 0 ∧
      ∀ (k : ℕ) (X : Matrix (Fin n) (Fin n) ℝ),
        relaxBodyLE (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) X →
        -(((0 : ℚ)) : ℝ) ≤ frob (castMat dM) (X - castMat cXp) := by
  obtain ⟨dM, hne, hsep⟩ := separator_of_not_mem hn A cXp u δ hδ h
  exact ⟨dM, hne, fun k X hX => hsep X hX⟩

/-- **Anchor 3, the `hbody` slot.**  At the sliver point `(G₁, t₁)` — nonempty real body, no
pinched member — every pinched rational centre is separated from the whole real relaxation by one
explicit nonzero rational direction. -/
theorem anchor3_separator (cXp : Matrix (Fin 2) (Fin 2) ℚ)
    (hdiag : ∀ i,
      cXp i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4) :
    ∃ dM : Matrix (Fin 2) (Fin 2) ℚ, dM ≠ 0 ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
        relaxBodyLE (castMat (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁))
          (((QMCLeafB.Audit2M5.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁ : ℚ)) : ℝ)
          (((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq : ℚ) : ℝ) X →
        -(((0 : ℚ)) : ℝ) ≤ frob (castMat dM) (X - castMat cXp) := by
  have hδ : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq :=
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).hdq
  have h : ¬ RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) cXp
      (QMCLeafB.Audit2M5.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq :=
    QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ cXp hdiag
  exact separator_of_not_mem (n := 2) (by norm_num)
    (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) cXp _ _ hδ h

/-- **Anchor 3, the threshold form**: the *same* direction serves every level `t' ≤ t₁` in the
bracket — the whole sliver below the exemplar, not just the exemplar. -/
theorem anchor3_separator_below (cXp : Matrix (Fin 2) (Fin 2) ℚ)
    (hdiag : ∀ i,
      cXp i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4) :
    ∃ dM : Matrix (Fin 2) (Fin 2) ℚ, dM ≠ 0 ∧
      ∀ t' : ℚ, t' ≤ QMCLeafB.Audit2M5.t₁ → ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
        relaxBodyLE (castMat (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁))
          (((t' - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁ : ℚ)) : ℝ)
          (((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq : ℚ) : ℝ) X →
        -(((0 : ℚ)) : ℝ) ≤ frob (castMat dM) (X - castMat cXp) := by
  have hδ : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq :=
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).hdq
  have h : ¬ RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) cXp
      (QMCLeafB.Audit2M5.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq :=
    QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ cXp hdiag
  obtain ⟨dM, hne, hsep⟩ := separator_below (n := 2) (by norm_num)
    (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) cXp
    (QMCLeafB.Audit2M5.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq hδ h
  refine ⟨dM, hne, fun t' ht' X hX =>
    hsep (t' - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁) ?_ X hX⟩
  linarith

/-! ## 5.  Falsification: the zero-depth / zero-margin stream is not stationary

The cheapest-looking repair at the open stratum is to re-present the cut stream at depth `0` and
margin `0`: then `RunParts.hcut` reads `0 ≤ c ⪝ (z - Cat k)`, `hcheck` is `0 ≤ 0`, and the whole
drift ledger seems to vanish.  It does not.  At depth `0` the engine's centre step is still

    stepCentre n a c p 0 = a + (gammaR n 0 / sqrtSigmaR c p) • p,    gammaR n 0 = 1/(n+1) ≠ 0,

so the coordinate `c ⪝ Cat k` — exactly the quantity `hcut` compares against the body — strictly
**increases** at every round.  A margin-`0` stream therefore cannot serve a multi-round window, and
the required margin grows while the cap `rho · sqrtSigmaR c p` is what the ledger has to pay. -/

/-- `gammaR` at depth `0`. -/
theorem gammaR_zero (n : ℕ) : QMCLeafB.EngineIterates.gammaR n 0 = 1 / ((n : ℝ) + 1) := by
  unfold QMCLeafB.EngineIterates.gammaR
  norm_num

/-- `gammaR` at depth `0` is nonzero, so the depth-`0` centre step is non-degenerate. -/
theorem gammaR_zero_ne (n : ℕ) : QMCLeafB.EngineIterates.gammaR n 0 ≠ 0 := by
  rw [gammaR_zero]
  positivity

/-- **The depth-`0` centre step strictly increases the cut-normal coordinate.** -/
theorem centre_coord_strict (n : ℕ) (a c p : Fin n → ℝ)
    (hσ : 0 < QMCLeafB.EngineIterates.sigmaR c p) :
    c ⬝ᵥ a < c ⬝ᵥ QMCLeafB.EngineIterates.stepCentre n a c p 0 := by
  have hsqrt : 0 < QMCLeafB.EngineIterates.sqrtSigmaR c p :=
    Real.sqrt_pos.mpr hσ
  have hg : 0 < QMCLeafB.EngineIterates.gammaR n 0 := by
    rw [gammaR_zero]
    positivity
  have hcoef : 0 < QMCLeafB.EngineIterates.gammaR n 0
      / QMCLeafB.EngineIterates.sqrtSigmaR c p := by positivity
  have hp : 0 < c ⬝ᵥ p := hσ
  rw [QMCLeafB.EngineIterates.stepCentre, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have : 0 < QMCLeafB.EngineIterates.gammaR n 0
      / QMCLeafB.EngineIterates.sqrtSigmaR c p * (c ⬝ᵥ p) := mul_pos hcoef hp
  linarith

/-- **The zero-margin reading is not stationary.**  In a depth-`0` cut stream with positive cut
norms, the normal coordinate of the engine's centre strictly increases at every round; since
`RunParts.hcut` compares that coordinate against the whole relaxation, a stream with `del ≡ 0`
cannot serve more than the rounds whose body still reaches below it. -/
theorem zeroMargin_not_stationary {n : ℕ} (cd : ℕ → QMCLeafB.EngineIterates.CutData n)
    (hρ : ∀ k, (cd k).rho = 0)
    (hσ : ∀ k, 0 < QMCLeafB.EngineIterates.sigmaR (QMCLeafB.EngineIterates.cutCR cd k)
      (QMCLeafB.EngineIterates.cutPR cd k)) :
    ∀ k : ℕ,
      QMCLeafB.EngineIterates.cutCR cd k
          ⬝ᵥ QMCLeafB.EngineIterates.Cat n (0 : Fin n → ℝ) cd k
        < QMCLeafB.EngineIterates.cutCR cd k
            ⬝ᵥ QMCLeafB.EngineIterates.Cat n (0 : Fin n → ℝ) cd (k + 1) := by
  intro k
  have hunf := QMCLeafB.EngineIterates.Cat_unfold (n := n) (0 : Fin n → ℝ) cd k
  have h0 : (((cd k).rho : ℚ) : ℝ) = 0 := by
    rw [hρ k]
    norm_num
  rw [hunf, h0]
  exact centre_coord_strict n _ _ _ (hσ k)

/-! ## 6.  What is left, named

`hbody` is now certificate data at a frozen window.  `dilCut`'s producer still owes, at the same
stream `cn k = c k + λ_k • flatQ dM`, the three slots `hdriftc`, `hlam1`, `hlam2`, and this one:

* `hdriftd` — `flatQ dM ⬝ (Cat k - flat cXp) ≤ 0`.

At the frozen window that is a statement purely about the *engine's* centre `Cat k` against the
fixed point `flat cXp`; it is the only remaining analytic content of the stratum and it is not
proved here. -/

/-- The residual `hdriftd` of `RunPartsDilate.dilCut` at a frozen recorded centre. -/
def FrozenDrift {n : ℕ} (dM : Matrix (Fin n) (Fin n) ℚ) (cXp : Matrix (Fin n) (Fin n) ℚ)
    (Cat : ℕ → (Fin (n * n) → ℝ)) : Prop :=
  ∀ k : ℕ,
    (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ))
        ⬝ᵥ (Cat k - QMCLeafB.AnswerProducer.flat (castMat cXp))
      ≤ 0

/-! ## 7.  Axiom receipt -/

#print axioms QMCLeafB.HBodyM6.relaxBodyLE_mono
#print axioms QMCLeafB.HBodyM6.relaxMem_mono
#print axioms QMCLeafB.HBodyM6.not_relaxMem_mono
#print axioms QMCLeafB.HBodyM6.body_empty_mono
#print axioms QMCLeafB.HBodyM6.oneMat_ne_zero
#print axioms QMCLeafB.HBodyM6.signOf_ne_zero
#print axioms QMCLeafB.HBodyM6.vecMulVec_self_ne_zero
#print axioms QMCLeafB.HBodyM6.frob_zero_left
#print axioms QMCLeafB.HBodyM6.gammaR_zero
#print axioms QMCLeafB.HBodyM6.gammaR_zero_ne
#print axioms QMCLeafB.HBodyM6.centre_coord_strict
#print axioms QMCLeafB.HBodyM6.zeroMargin_not_stationary
#print axioms QMCLeafB.HBodyM6.separator_of_not_mem
#print axioms QMCLeafB.HBodyM6.separator_below
#print axioms QMCLeafB.HBodyM6.hbody_frozen_window
#print axioms QMCLeafB.HBodyM6.anchor3_separator
#print axioms QMCLeafB.HBodyM6.anchor3_separator_below
#print axioms QMCLeafB.HBodyM6.FrozenDrift

end QMCLeafB.HBodyM6


