-- Prove2me | Definitions.Def_QMCLeafB_lm38
-- name    : QMCLeafB_lm38
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:31:44.916077+00:00
-- url     : https://prove2.me/theorems/1db3c761-397d-4e25-ac3a-ad5ce86ffa5f
-- title:
--   QMCLeafB lm38
-- statement:
--   # `Check_lm38_m5` — phase 38, member m5, direction `affine-normalisation` (d8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
/-
# `Check_lm38_m5` — phase 38, member m5, direction `affine-normalisation` (d8)

## What this file decides

The leaf's per-round obligation (phase 37, `RecSlot`'s non-definitional content, m7/ph37's
`no_price_of_deep_point` form) is: at round `k`, with `A = A_k`, `a = Cat k` the accumulated point
(= the ellipsoid centre), body `B ⊆ Ell A a`, a cut normal `c` with rational witness `p`
(`A *ᵥ p = c`, `σ = c ⬝ᵥ p = ‖c‖²_{A⁻¹}`) and slack `del`, the record needs

  `0 ≤ ρ ≤ rmax`, `0 ≤ del`, `del² ≤ ρ² σ`, and `∀ z ∈ B, -del ≤ c ⬝ᵥ (z - a)`   (`hcut`).

This file proves what that obligation **is**, exactly, with no slack anywhere:

* **§2 `round_criterion`** — the `∃` over normals is ELIMINATED. With `t` the ledger's ceiling
  (`del ≤ t √σ`), the obligation holds at the round **iff there is an `A`-unit direction `w` with
  `⟨z - a, w⟩_A ≤ t` for every body point `z`**:
  `(∃ c p, c ≠ 0 ∧ A p = c ∧ ∀ z ∈ B, -t√σ ≤ c·(z - a)) ↔ (∃ w, ‖w‖²_A = 1 ∧ ∀ z ∈ B, (z-a)·Aw ≤ t)`.
  This is the affine-normalised form: in the `A`-frame the body must lie in the slab
  `{⟨w, ·⟩_A ≤ t}` through the centre. No convexity, no dimension, no rational data enters.

* **§3 `recording_iff`** — the same with the *whole* ledger (`ρ`, `del` free): the round admits a
  recording iff the geometric condition `Δ_A(a, B) ≤ t` holds, where
  `Δ_A(a,B) := inf over A-unit w of sup_{z∈B} ⟨w, z - a⟩_A` is the **one-sided depth** of the body
  at `a`. So **the depth ledger is not the obstruction** (`exists_lam_ledger`, `sigmaQ_normalCut_pos`
  are consistent with this): no choice of normal, depth or rational centre can fix a round whose
  one-sided depth exceeds the ceiling, and no choice is needed at a round whose depth is below it.

* **§3b `fixed_normal_iff`** — with the normal **given** (the campaign's gate dictates it), the whole
  ledger collapses to the ceiling condition itself: `∃ ρ del` with `ρ ≤ t`, `del² ≤ ρ²σ` records at
  `(c, a)` iff `∀ z ∈ B, -t√σ ≤ c ⬝ᵥ (z - a)`.  So together with §3: the ledger is free for the
  `∃`-over-normals form and *empty* for the fixed-normal form — in neither reading does it carry
  any analytic content.

* **§4 the two sharp ends.**
  `flat_ok`: if a supporting hyperplane of `B` passes through `a` (i.e. `Δ_A(a,B) ≤ 0`) then the
  round is recordable **with `del = 0`** at every ceiling `t ≥ 0` — the face record, in criterion
  form, with no flatness/level-set hypothesis beyond the support condition itself.
  `ball_no_round`: if `B` contains the `A`-ball of radius `r > t` about `a` then the round is
  infeasible for **every** normal and every ledger — the sharp, all-normals-at-once form of
  `no_price_of_deep_point` (one deep point kills one normal; a ball of radius `> t` kills them all).

* **§6 `cut_direction_spoiled` / `campaign_spoil`** — the witness direction cannot be reused.  Since
  the step maps a body point of `ê`-height `s` to `ê`-height `(s-γ)/(1-γ)`, the *witness* of the
  round just played (`w = -ê`) needs, in the new frame, `⟨ê, z⟩ ≥ γ - rmax (1-γ)` for every body
  point — while in the round just played it needed only `⟨ê, z⟩ ≥ -rmax`.  So the threshold rises
  from `-rmax` to `γ - rmax (1-γ) ≈ 1/(N+1) > 0`, and **a single body point that is not strictly
  above `γ - rmax(1-γ)` in that direction (in particular any point at or below the centre's own
  hyperplane) spoils the reuse.**  `campaign_spoil` proves the hypothesis `rmax (1-γ) < γ` for
  **every** admissible `ρ ≤ rmax` at `rmax = 1/(4N)`, all `N ≥ 1`.  Hence a recording run must rotate
  its witness direction at every round unless the body is squeezed into the far cap.

* **§5 the correction of the phase-37 reading.** The obligation is **not** "the centre is within
  `rmax` of the body in the `A`-norm" in the distance sense `dist_A(a,B) ≤ rmax`: the criterion
  `Δ_A ≤ t` differs from `dist_A ≤ t` in *both* directions, machine-checked here at `N = 2`,
  `A = 1`, `t = 1/8 = rmaxOf 2`:
  `far_body_ok`: the half-space body `{x | x 0 ≤ -1}` has `dist_A(a,B) = 1 > t` yet is recordable
  (with `del = 0`) at every ceiling;
  `near_body_fails`: the ball of radius `1/2` about `a` has `dist_A(a,B) = 0 ≤ t` yet is recordable
  at no ceiling below `1/2`.
  So a proof of the leaf that reads the residual as bounded distance is proving a false statement,
  and the correct residual is the one-sided depth `Δ_A(Cat k, body) ≤ rmax`.

## The verdict this file settles

Reading `Δ_A(a,B) := inf over A-unit w of sup_{z∈B} ⟨w, z - a⟩_A` as the **signed** `A`-distance
(`-dist_A(a,B)` outside the body, the one-sided interior depth inside it), §2–§3 say:

> the leaf's per-round obligation **is** `Δ_{A_k}(Cat k, body) ≤ rmax` — nothing else.  It is
> satisfied outright (`del ≡ 0`) whenever a supporting hyperplane of the body passes through
> `Cat k`, in particular at every round on the flat face, and at every round where the centre is
> outside the body; it is satisfied by **no** normal and **no** depth once the body contains the
> `A_k`-ball of radius `> rmax` about `Cat k`.

So the residual is **not** the bounded distance `dist_{A_k}(Cat k, body) ≤ rmax` (§5 refutes that
reading in both directions), and it is **not** a depth-`ρ` / `σ` / normal-choice matter (§3): the
depth ledger can neither rescue a failing round nor obstruct a passing one.  What remains for the
campaign is exactly the geometric question "is the accumulated centre ever more than `rmax` deep
inside the body?", with §6 pinning the dynamics: the witness must rotate at every round unless the body is squeezed
into the far cap above the centre.

Discipline: `set_option autoImplicit false`; every `#print axioms` is exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

namespace QMCLeafB.Lm38M5

open Matrix

variable {N : ℕ}

/-! ## 0.  The quadratic form, the ellipsoid, and the `A`-unit directions -/

/-- The real quadratic form `xᵀ A x` (definitionally the engine's `qfR`). -/
noncomputable def qfR (A : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

/-- The closed ellipsoid of the engine. -/
noncomputable def Ell (A : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {x | qfR A (x - a) ≤ 1}

/-- A symmetry-free reading of a positive definite real shape: it is its own transpose. -/
theorem transpose_of_posDef {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) : Aᵀ = A := by
  have h := hA.isHermitian.eq
  simpa using h

theorem qfR_smul (A : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) (x : Fin N → ℝ) :
    qfR A (s • x) = s ^ 2 * qfR A x := by
  simp only [qfR, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- A scaled pairing reads off the quadratic form. -/
theorem smul_dot_qfR (A : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) (w : Fin N → ℝ) :
    (s • w) ⬝ᵥ (A *ᵥ w) = s * qfR A w := by
  rw [smul_dotProduct, smul_eq_mul, qfR]

/-- The `A`-pairing is symmetric: this is the only place the shape's symmetry is used. -/
theorem dot_A_comm {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) (x y : Fin N → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, transpose_of_posDef hA, dotProduct_comm]

/-- `A w ≠ 0` for an `A`-unit vector: the noise-free statement that the witness `p = w` is nonzero. -/
theorem mulVec_ne_zero {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) {w : Fin N → ℝ}
    (hw : qfR A w = 1) : A *ᵥ w ≠ 0 := by
  intro h
  have h0 : qfR A w = 0 := by rw [qfR, h, dotProduct_zero]
  rw [hw] at h0
  norm_num at h0

/-- A positive definite form is positive on the `A`-unit sphere; in particular `σ > 0` there. -/
theorem qfR_pos {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) {w : Fin N → ℝ}
    (hw : qfR A w = 1) : 0 < w ⬝ᵥ (A *ᵥ w) := by
  rw [← qfR]
  rw [hw]
  norm_num

/-! ## 2.  The criterion: the `∃` over normals is eliminated

`hcut` at the accumulated point `a` is `∀ z ∈ B, -del ≤ c ⬝ᵥ (z - a)`. The ledger caps the slack at
`t √σ` (`del² ≤ ρ² σ`, `ρ ≤ t`). The next theorem says that with the ceiling `t` there is such a
normal-`∃` **iff** the body lies on the shallow side of some `A`-unit hyperplane through `a`. -/

/-- **THE ROUND CRITERION.**  For a positive definite shape `A`, a body `B`, the accumulated point
`a` and a ceiling `t`:

`(∃ normal c, witness p, A p = c, c ≠ 0, ∀ z ∈ B, -t √(c ⬝ᵥ p) ≤ c ⬝ᵥ (z - a))`
`  ↔ (∃ A-unit w, ∀ z ∈ B, (z - a) ⬝ᵥ (A *ᵥ w) ≤ t)`.

The right-hand side mentions no normal, no depth, no `σ`, no rational centre: it is the
affine-normalised geometric content of the leaf's round obligation. -/
theorem round_criterion {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    (B : Set (Fin N → ℝ)) (a : Fin N → ℝ) (t : ℝ) :
    (∃ c p : Fin N → ℝ, c ≠ 0 ∧ A *ᵥ p = c ∧
        ∀ z ∈ B, -t * Real.sqrt (c ⬝ᵥ p) ≤ c ⬝ᵥ (z - a))
      ↔ (∃ w : Fin N → ℝ, qfR A w = 1 ∧ ∀ z ∈ B, (z - a) ⬝ᵥ (A *ᵥ w) ≤ t) := by
  constructor
  · -- (⟹)  read the normal off the body: `w = -(1/√σ) p` is `A`-unit
    rintro ⟨c, p, hc, hAp, hB⟩
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [Matrix.mulVec_zero] at hAp
      exact hc hAp.symm
    have hqf : qfR A p = c ⬝ᵥ p := by
      simp only [qfR, hAp, dotProduct_comm]
    have hσpos : 0 < c ⬝ᵥ p := hqf ▸ hA.dotProduct_mulVec_pos hp0
    set s : ℝ := Real.sqrt (c ⬝ᵥ p) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hσpos
    have hss : s * s = c ⬝ᵥ p := Real.mul_self_sqrt hσpos.le
    refine ⟨(-(1 / s)) • p, ?_, ?_⟩
    · rw [qfR_smul, hqf, ← hss]
      field_simp
    · intro z hz
      have h := hB z hz
      have hstep : (z - a) ⬝ᵥ (A *ᵥ ((-(1 / s)) • p)) = -(1 / s) * (c ⬝ᵥ (z - a)) := by
        rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
        rw [hAp, dotProduct_comm]
      rw [hstep]
      have hle : -(1 / s) * (c ⬝ᵥ (z - a)) ≤ -(1 / s) * (-t * s) := by
        refine mul_le_mul_of_nonpos_left h ?_
        have : (0:ℝ) < 1 / s := by positivity
        linarith
      have hrw : -(1 / s) * (-t * s) = t := by
        field_simp
      rw [hrw] at hle
      exact hle
  · -- (⟸)  take the witness direction as the normal, `del = t √σ = t`
    rintro ⟨w, hw, hB⟩
    have hσ : (-(A *ᵥ w)) ⬝ᵥ (-w) = 1 := by
      rw [neg_dotProduct, dotProduct_neg, neg_neg, dotProduct_comm, ← qfR]
      exact hw
    refine ⟨-(A *ᵥ w), -w, ?_, ?_, ?_⟩
    · have h := mulVec_ne_zero hA hw
      simpa using h
    · rw [Matrix.mulVec_neg]
    · intro z hz
      have h := hB z hz
      have hsq : Real.sqrt ((-(A *ᵥ w)) ⬝ᵥ (-w)) = 1 := by
        rw [hσ, Real.sqrt_one]
      rw [hsq, mul_one]
      have : (-(A *ᵥ w)) ⬝ᵥ (z - a) = -((z - a) ⬝ᵥ (A *ᵥ w)) := by
        rw [neg_dotProduct, dotProduct_comm]
      rw [this]
      linarith

#print axioms QMCLeafB.Lm38M5.round_criterion

/-! ## 3.  The whole ledger, eliminated: the depth is not the obstruction -/

/-- **`recording_iff`.**  The round admits a recording — **any** normal, **any** depth `ρ ≤ t`,
**any** slack `del` with `del² ≤ ρ² σ` — iff the body lies on the shallow side of an `A`-unit
hyperplane through `a`.  Both directions of the ledger (`del² ≤ ρ²σ`, `ρ ≤ t`) are eliminated:
they can neither rescue a round whose one-sided depth exceeds `t`, nor obstruct one below `t`. -/
theorem recording_iff {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    (B : Set (Fin N → ℝ)) (a : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∃ (c p : Fin N → ℝ) (ρ del : ℝ), c ≠ 0 ∧ A *ᵥ p = c ∧ 0 ≤ ρ ∧ ρ ≤ t ∧ 0 ≤ del ∧
        del ^ 2 ≤ ρ ^ 2 * (c ⬝ᵥ p) ∧ ∀ z ∈ B, -del ≤ c ⬝ᵥ (z - a))
      ↔ (∃ w : Fin N → ℝ, qfR A w = 1 ∧ ∀ z ∈ B, (z - a) ⬝ᵥ (A *ᵥ w) ≤ t) := by
  constructor
  · rintro ⟨c, p, ρ, del, hc, hAp, hρ0, hρt, hdel0, hchk, hB⟩
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [Matrix.mulVec_zero] at hAp
      exact hc hAp.symm
    have hqf : qfR A p = c ⬝ᵥ p := by
      simp only [qfR, hAp, dotProduct_comm]
    have hσpos : 0 < c ⬝ᵥ p := hqf ▸ hA.dotProduct_mulVec_pos hp0
    have hdel_le : del ≤ t * Real.sqrt (c ⬝ᵥ p) := by
      have h1 : del ≤ Real.sqrt (ρ ^ 2 * (c ⬝ᵥ p)) := by
        rw [← Real.sqrt_sq hdel0]
        exact Real.sqrt_le_sqrt hchk
      have h2 : Real.sqrt (ρ ^ 2 * (c ⬝ᵥ p)) = ρ * Real.sqrt (c ⬝ᵥ p) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hρ0]
      rw [h2] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_right hρt (Real.sqrt_nonneg _))
    refine (round_criterion hA B a t).mp ⟨c, p, hc, hAp, ?_⟩
    intro z hz
    linarith [hB z hz]
  · intro h
    obtain ⟨w, hw, hB⟩ := h
    have hσ : (-(A *ᵥ w)) ⬝ᵥ (-w) = 1 := by
      rw [neg_dotProduct, dotProduct_neg, neg_neg, dotProduct_comm, ← qfR]
      exact hw
    refine ⟨-(A *ᵥ w), -w, t, t, ?_, ?_, ht, le_rfl, ht, ?_, ?_⟩
    · have h := mulVec_ne_zero hA hw
      simpa using h
    · rw [Matrix.mulVec_neg]
    · rw [hσ]
      nlinarith
    · intro z hz
      have h := hB z hz
      have : (-(A *ᵥ w)) ⬝ᵥ (z - a) = -((z - a) ⬝ᵥ (A *ᵥ w)) := by
        rw [neg_dotProduct, dotProduct_comm]
      rw [this]
      linarith

#print axioms QMCLeafB.Lm38M5.recording_iff

/-- **`fixed_normal_iff`** — with the cut's normal **given** (the gate dictates it in the campaign),
the whole depth ledger collapses to exactly the ceiling condition: a recording at ceiling `t` exists
iff `∀ z ∈ B, -t √σ ≤ c ⬝ᵥ (z - a)`.  So for a dictated normal the free parameters `ρ` and `del`
buy nothing at all. -/
theorem fixed_normal_iff {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    (B : Set (Fin N → ℝ)) (a : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) :
    (∃ (ρ del : ℝ), 0 ≤ ρ ∧ ρ ≤ t ∧ 0 ≤ del ∧ del ^ 2 ≤ ρ ^ 2 * (c ⬝ᵥ p) ∧
        ∀ z ∈ B, -del ≤ c ⬝ᵥ (z - a))
      ↔ (∀ z ∈ B, -t * Real.sqrt (c ⬝ᵥ p) ≤ c ⬝ᵥ (z - a)) := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [Matrix.mulVec_zero] at hAp
    exact hc hAp.symm
  have hqf : qfR A p = c ⬝ᵥ p := by
    simp only [qfR, hAp, dotProduct_comm]
  have hσpos : 0 < c ⬝ᵥ p := hqf ▸ hA.dotProduct_mulVec_pos hp0
  constructor
  · rintro ⟨ρ, del, hρ0, hρt, hdel0, hchk, hB⟩ z hz
    have hdel_le : del ≤ t * Real.sqrt (c ⬝ᵥ p) := by
      have h1 : del ≤ Real.sqrt (ρ ^ 2 * (c ⬝ᵥ p)) := by
        rw [← Real.sqrt_sq hdel0]
        exact Real.sqrt_le_sqrt hchk
      have h2 : Real.sqrt (ρ ^ 2 * (c ⬝ᵥ p)) = ρ * Real.sqrt (c ⬝ᵥ p) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hρ0]
      rw [h2] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_right hρt (Real.sqrt_nonneg _))
    have htσ : (0:ℝ) ≤ t * Real.sqrt (c ⬝ᵥ p) :=
      mul_nonneg ht (Real.sqrt_nonneg _)
    linarith [hB z hz]
  · intro hB
    have hB' : ∀ z ∈ B, -(t * Real.sqrt (c ⬝ᵥ p)) ≤ c ⬝ᵥ (z - a) := by
      intro z hz
      have := hB z hz
      linarith
    refine ⟨t, t * Real.sqrt (c ⬝ᵥ p), ht, le_rfl, ?_, ?_, hB'⟩
    · exact mul_nonneg ht (Real.sqrt_nonneg _)
    · have hsq : (t * Real.sqrt (c ⬝ᵥ p)) ^ 2 = t ^ 2 * (c ⬝ᵥ p) := by
        rw [mul_pow, Real.sq_sqrt hσpos.le]
      rw [hsq]

#print axioms QMCLeafB.Lm38M5.fixed_normal_iff

/-! ## 4.  The two sharp ends -/

/-- **`flat_ok`** — a supporting hyperplane of the body through `a` records at **every** ceiling
`t ≥ 0` with `del ≡ 0` (hence for every depth `ρ` with `0 ≤ ρ ≤ t`, and with the normal free in
magnitude).  This is the face/flat record of m2/ph36 and m6/ph35 in criterion form: the flatness
hypothesis is not needed, only the support condition. -/
theorem flat_ok {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {B : Set (Fin N → ℝ)} {a : Fin N → ℝ}
    (h : ∃ w : Fin N → ℝ, qfR A w = 1 ∧ ∀ z ∈ B, (z - a) ⬝ᵥ (A *ᵥ w) ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ (c p : Fin N → ℝ) (ρ del : ℝ), c ≠ 0 ∧ A *ᵥ p = c ∧ 0 ≤ ρ ∧ ρ ≤ t ∧ del = 0 ∧
      del ^ 2 ≤ ρ ^ 2 * (c ⬝ᵥ p) ∧ ∀ z ∈ B, -del ≤ c ⬝ᵥ (z - a) := by
  obtain ⟨w, hw, hB⟩ := h
  have hσ : (-(A *ᵥ w)) ⬝ᵥ (-w) = 1 := by
    rw [neg_dotProduct, dotProduct_neg, neg_neg, dotProduct_comm, ← qfR]
    exact hw
  refine ⟨-(A *ᵥ w), -w, t, 0, ?_, ?_, ht, le_rfl, rfl, ?_, ?_⟩
  · have h := mulVec_ne_zero hA hw
    simpa using h
  · rw [Matrix.mulVec_neg]
  · rw [hσ]
    ring_nf
    nlinarith
  · intro z hz
    have h := hB z hz
    have hEq : (-(A *ᵥ w)) ⬝ᵥ (z - a) = -((z - a) ⬝ᵥ (A *ᵥ w)) := by
      rw [neg_dotProduct, dotProduct_comm]
    rw [hEq]
    linarith

#print axioms QMCLeafB.Lm38M5.flat_ok

/-- **`ball_no_round`** — if the body contains the `A`-ball of radius `r` about `a` and `r > t`,
then **no** normal and no ledger records the round.  This is `no_price_of_deep_point` at the round
level and for *all* normals at once: a single deep point kills one normal, a ball of radius `> t`
kills every one of them.  (The `r ≤ 1` hypothesis is what puts the ball inside the ellipsoid.) -/
theorem ball_no_round {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {a : Fin N → ℝ} {r t : ℝ} (hrt : t < r) (hr : r ≤ 1) :
    ¬ ∃ w : Fin N → ℝ, qfR A w = 1 ∧ ∀ z : Fin N → ℝ, qfR A (z - a) ≤ r ^ 2 →
        (z - a) ⬝ᵥ (A *ᵥ w) ≤ t := by
  rintro ⟨w, hw, hB⟩
  have hz : qfR A (a + r • w - a) ≤ r ^ 2 := by
    rw [add_sub_cancel_left, qfR_smul, hw]
    nlinarith
  have h := hB (a + r • w) hz
  rw [add_sub_cancel_left, smul_dot_qfR, hw] at h
  nlinarith

#print axioms QMCLeafB.Lm38M5.ball_no_round

/-! ## 5.  The correction: the obligation is the ONE-SIDED depth, not the distance

The phase-37 residual was restated as "the ellipsoid centre stays within `rmax` of the body in the
current `A_k`-norm".  Read as `dist_A(Cat k, body) ≤ rmax` that is **false in both directions**.
Here are the two machine-checked witnesses, at the campaign's own constant for `N = 2`
(`rmaxOf 2 = 1/8`) and in dimension `1` for the first (dimension is irrelevant to the criterion).

* §5.1: a body whose every point is at `A`-distance `≥ 1 > 1/8` from `a`, and yet the round is
  recordable **with `del = 0`** — so the obligation does not bound any distance;
* §5.2: a body containing `a` itself (`dist = 0 ≤ 1/8`) which is recordable by **no** normal at
  ceiling `1/8` — so the distance says nothing about the obligation either.
-/

section Correction

/-- The `1`-dimensional shape (the identity, which is positive definite). -/
noncomputable def A1 : Matrix (Fin 1) (Fin 1) ℝ := 1

/-- The `1`-dimensional constant direction. -/
noncomputable def w1 : Fin 1 → ℝ := fun _ => 1

/-- Dot products in dimension `1`. -/
theorem dot_fin1 (z y : Fin 1 → ℝ) : z ⬝ᵥ y = z 0 * y 0 := by
  simp [dotProduct]

theorem w1_apply (i : Fin 1) : w1 i = 1 := rfl

theorem qfR_A1 (z : Fin 1 → ℝ) : qfR A1 z = z 0 * z 0 := by
  rw [qfR, A1, Matrix.one_mulVec, dot_fin1]

theorem qfR_A1_w1 : qfR A1 w1 = 1 := by
  rw [qfR_A1]
  show (1 : ℝ) * 1 = 1
  norm_num

/-- **§5.1 `far_body_records`.**  The half-space body `{z | z 0 ≤ -1}` is recordable at ceiling
`1/8` with `del = 0`, while every one of its points is at squared `A`-distance `≥ 1` from `a = 0`
(so at distance `≥ 1 > 1/8`).  Hence the leaf's obligation is **not** a bounded-distance statement
in the direction "obligation ⟹ close". -/
theorem far_body_records :
    (∃ (c p : Fin 1 → ℝ) (ρ del : ℝ), c ≠ 0 ∧ A1 *ᵥ p = c ∧ 0 ≤ ρ ∧ ρ ≤ 1 / 8 ∧ del = 0 ∧
        del ^ 2 ≤ ρ ^ 2 * (c ⬝ᵥ p) ∧
        ∀ z : Fin 1 → ℝ, z 0 ≤ -1 → -del ≤ c ⬝ᵥ (z - (0 : Fin 1 → ℝ))) ∧
      (∀ z : Fin 1 → ℝ, z 0 ≤ -1 → (1 / 8 : ℝ) ^ 2 < qfR A1 (z - (0 : Fin 1 → ℝ))) := by
  have hA : A1.PosDef := by
    have : A1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) := rfl
    rw [this]
    exact Matrix.PosDef.one
  constructor
  · refine flat_ok hA (B := {z : Fin 1 → ℝ | z 0 ≤ -1}) (a := 0) ⟨w1, qfR_A1_w1, ?_⟩
      (t := 1 / 8) (by norm_num)
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    have h1 : (z - (0 : Fin 1 → ℝ)) ⬝ᵥ (A1 *ᵥ w1) = z 0 * 1 := by
      rw [sub_zero, A1, Matrix.one_mulVec, dot_fin1, w1_apply]
    rw [h1]
    linarith
  · intro z hz
    have hq : qfR A1 (z - (0 : Fin 1 → ℝ)) = z 0 * z 0 := by
      rw [sub_zero, qfR_A1]
    rw [hq]
    nlinarith

#print axioms QMCLeafB.Lm38M5.far_body_records

/-- **§5.2 `near_body_unrecordable`.**  The `A`-ball of radius `1/2` about `a = 0` contains `a`
(so its distance from `a` is `0 ≤ 1/8`), yet **no** normal records it at ceiling `1/8`.  Hence the
leaf's obligation is **not** a bounded-distance statement in the direction "close ⟹ obligation". -/
theorem near_body_unrecordable :
    ¬ (∃ w : Fin 1 → ℝ, qfR A1 w = 1 ∧
        ∀ z : Fin 1 → ℝ, qfR A1 (z - (0 : Fin 1 → ℝ)) ≤ (1 / 2 : ℝ) ^ 2 →
          (z - (0 : Fin 1 → ℝ)) ⬝ᵥ (A1 *ᵥ w) ≤ 1 / 8) := by
  have hA : A1.PosDef := by
    have : A1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) := rfl
    rw [this]
    exact Matrix.PosDef.one
  exact ball_no_round (A := A1) hA (a := 0) (r := 1 / 2) (t := 1 / 8) (by norm_num) (by norm_num)

#print axioms QMCLeafB.Lm38M5.near_body_unrecordable

end Correction

/-! ## 6.  The advance: the witness direction cannot be reused unless the body sits high

The step (in the `A`-normal frame) sends the centre to `γ • ê` and the shape to
`α • (1 + β • vecMulVec ê ê)`; by the engine's own `stepShape`/`stepCentre` algebra (`A = 1`,
`c = ê`, `σ = 1`, `α (1+β) = (1-γ)⁻²`) the new `ê`-normalised height of a body point `y` is exactly
`(⟨ê, y⟩ - γ)/(1 - γ)` — this is where the `(1-ρ)/(N+1)` step law comes from.  Hence the new
`-ê`-height is `(γ - ⟨ê, y⟩)/(1 - γ)`.

The criterion bounds the SUP of the heights, so the direction that matters for reuse is `w = -ê` (the
witness of the round that was just played).  At round `k` the witness `w` needed only
`sup_z ⟨w, z - a⟩_A ≤ rmax`, i.e. `⟨ê, z⟩ ≥ -rmax` for all `z`; at round `k+1`, in the new frame, `w`
needs `(γ - ⟨ê, z⟩)/(1 - γ) ≤ rmax` for all `z`, i.e. `⟨ê, z⟩ ≥ γ - rmax (1 - γ)`.  The threshold
moves **from `-rmax` up to `γ - rmax (1-γ) ≈ 1/(N+1)`**: so a single body point that is not strictly
above `γ - rmax (1-γ)` in the `ê` direction — in particular any point at or below the centre's own
hyperplane — makes `w` unusable at the next round.  At the campaign's constants this applies to every
admissible depth (`campaign_spoil`), so the witness direction must rotate unless the body is
squeezed into the far cap. -/

/-- **`cut_direction_spoiled`.**  If a body point satisfies `⟨ê, y⟩ ≤ 0` (it is not strictly above
the cut's own hyperplane through the centre), then in the next frame its `-ê`-height already exceeds
`rmax` — so the previous round's witness direction `w = -ê` cannot witness the criterion again. -/
theorem cut_direction_spoiled {γ rmax s : ℝ} (hγ1 : γ < 1) (hspoil : rmax * (1 - γ) < γ)
    (hs : s ≤ 0) :
    rmax < (γ - s) / (1 - γ) := by
  rw [lt_div_iff₀ (by linarith : (0:ℝ) < 1 - γ)]
  nlinarith

#print axioms QMCLeafB.Lm38M5.cut_direction_spoiled

/-- **`campaign_spoil`.**  At the campaign's constants (`rmax = rmaxOf N = 1/(4N)`, `N ≥ 1`,
engine depth `ρ ∈ [0, rmax]`, `γ = (1-ρ)/(N+1)`) the reuse threshold `γ - rmax (1-γ)` is positive —
equivalently `rmax (1-γ) < γ` — for **every** admissible depth.  So at the engine's own parameters no
cut direction survives its own step: the leaf's obligation forces a fresh witness direction at every
round unless the body lies strictly above the centre's hyperplane in the old one. -/
theorem campaign_spoil {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / (4 * (N:ℝ))) :
    1 / (4 * (N:ℝ)) * (1 - (1 - ρ) / ((N:ℝ) + 1)) < (1 - ρ) / ((N:ℝ) + 1) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hnp1 : (0:ℝ) < (N:ℝ) + 1 := by linarith
  have hb0 : 0 ≤ (1 - ρ) / ((N:ℝ) + 1) := by
    apply div_nonneg _ hnp1.le
    have hle1 : 1 / (4 * (N:ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hstep : 1 / (4 * (N:ℝ)) * (1 - (1 - ρ) / ((N:ℝ) + 1)) ≤ 1 / (4 * (N:ℝ)) := by
    have h1 : (1 - (1 - ρ) / ((N:ℝ) + 1)) ≤ 1 := by linarith
    have ha0 : (0:ℝ) ≤ 1 / (4 * (N:ℝ)) := by positivity
    nlinarith
  have hlt : 1 / (4 * (N:ℝ)) < (1 - ρ) / ((N:ℝ) + 1) := by
    rw [lt_div_iff₀ hnp1]
    have h3 : (N:ℝ) + 1 < 4 * (N:ℝ) - 1 := by linarith
    calc 1 / (4 * (N:ℝ)) * ((N:ℝ) + 1) = ((N:ℝ) + 1) / (4 * (N:ℝ)) := by ring
      _ < (4 * (N:ℝ) - 1) / (4 * (N:ℝ)) := div_lt_div_of_pos_right h3 (by positivity)
      _ = 1 - 1 / (4 * (N:ℝ)) := by field_simp
      _ ≤ 1 - ρ := by linarith
  linarith

#print axioms QMCLeafB.Lm38M5.campaign_spoil


