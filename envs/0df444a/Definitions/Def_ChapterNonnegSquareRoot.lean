-- Prove2me | Definitions.Def_ChapterNonnegSquareRoot
-- name    : ChapterNonnegSquareRoot
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T13:21:33.8563+00:00
-- url     : https://prove2.me/theorems/97c0015e-9685-4ab7-baf2-d91880f823d5
-- title:
--   Chapter NonnegSquareRoot
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNonnegSquareRoot.lean`): generated def bundle for ChapterNonnegSquareRoot. See BookProof/ChapterNonnegSquareRoot.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNonnegSquareRoot.lean

import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_nonneg

import Definitions.Def_ChapterPositiveSquareRootUnique
import Theorems.Thm_BookProof_FriedrichsSquare_adjPairs_factorRel
import Definitions.Def_ChapterUnboundedPolar
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterVonNeumannCore
import Mathlib


/-!
# The square root of an arbitrary non-negative self-adjoint linear relation

`BookProof.ChapterUnboundedPolar` constructs `|Ā| = (A* Ā)^{1/2}` and
`BookProof.ChapterPositiveSquareRootUnique` shows it is *the* non-negative
self-adjoint square root of `A* Ā`.  Both statements are about the particular
relation `factorRel A = A* Ā`.  This module removes that restriction:

> **Every non-negative self-adjoint linear relation `T` on a complex Hilbert
> space has a unique non-negative self-adjoint square root.**

The construction is the same bounded one, applied to the resolvent
`C = (1 + T)⁻¹ = invCLM hT`, which `ChapterPositiveSquareRootUnique` already
produces as an everywhere-defined positive contraction:

* `sqrtRel hT = {(C^{1/2} y, (1 − C)^{1/2} y) : y}` — formally
  `(1 − C)^{1/2} C^{−1/2} = ((C⁻¹ − 1))^{1/2} = T^{1/2}`;
* it is symmetric, `1 + T^{1/2}` is surjective, hence `T^{1/2}` is self-adjoint
  (`adjPairs_sqrtRel`), and it is non-negative
  (`isNonnegSelfAdjoint_sqrtRel`);
* **`(T^{1/2})² = T`** (`sqrtRel_comp_self`);
* **uniqueness** (`eq_sqrtRel_of_isNonnegSelfAdjoint`): if `S` is non-negative
  self-adjoint with `S S ⊆ T`, then `S = T^{1/2}`.  As in the special case, this
  is obtained from the *bounded* continuous functional calculus alone: with
  `C_S = (1 + S)⁻¹` one has the bounded identity
  `(1 + T)⁻¹ (1 − 2C_S + 2C_S²) = C_S²` (`invCLM_mul_den`), which on
  `spectrum C_S ⊆ [0,1]` says `(1 + T)⁻¹ = g(C_S)` for `g t = t²/(2t² − 2t + 1)`,
  and `g` is inverted there by `ψ r = √r/(√r + √(1−r))`, so
  `C_S = ψ((1 + T)⁻¹)` is determined by `T` alone.

`sqrtRel_unique_nonneg_sqrt` packages existence, the square, and uniqueness, and
`absRel_eq_sqrtRel` identifies the earlier `|Ā|` with `(A* Ā)^{1/2}` in this
sense.  Single-valuedness is inherited: if `T` is an operator, so is `T^{1/2}`
(`sqrtRel_snd_eq_zero_of_fst_eq_zero`).

Two further consequences are recorded.

* **The form of `T`.**  `D(T) ⊆ D(T^{1/2})` (`exists_mem_sqrtRel_of_mem`) and, for
  single-valued `T`, `⟪x, T x⟫ = ‖T^{1/2} x‖²` (`inner_eq_norm_sq_of_mem`,
  `norm_sq_eq_inner_of_mem`).
* **Commutation.**  A bounded operator commuting with `(1 + T)⁻¹` leaves both `T`
  and `T^{1/2}` invariant (`mem_of_commute`, `mem_sqrtRel_of_commute`).
* **The resolvent at every negative real.**  A positive real multiple `c T`
  (`smulRel`) of a non-negative self-adjoint relation is again one
  (`isNonnegSelfAdjoint_smulRel`, via `adjPairs_smulRel`), so the resolvent of
  `a⁻¹ T` gives, for every `a > 0`, an everywhere-defined bounded `(T + a)⁻¹`
  (`invCLMAt`) solving `a x + T x = h` uniquely (`invCLMAt_mem`,
  `invCLMAt_eq_of_mem`, `existsUnique_smul_add_mem`) with `‖(T + a)⁻¹‖ ≤ 1/a`
  (`norm_invCLMAt_le`): the spectrum of `T` misses the negative reals.
-/

namespace BookProof.NonnegSquareRoot

open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.FriedrichsSquare BookProof.VonNeumannCore BookProof.UnboundedPolar
open BookProof.PositiveSquareRoot
open scoped ComplexOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T S : Submodule ℂ (F × F)}

/-! ## The construction -/

/-- `C^{1/2}` for the resolvent `C = (1 + T)⁻¹`. -/
noncomputable def sqrtB (hT : IsNonnegSelfAdjoint T) : F →L[ℂ] F := sqrtOp (invCLM hT)

/-- `(1 − C)^{1/2}` for the resolvent `C = (1 + T)⁻¹`. -/
noncomputable def sqrtC (hT : IsNonnegSelfAdjoint T) : F →L[ℂ] F := coSqrtOp (invCLM hT)

/-- **The square root `T^{1/2}`** of a non-negative self-adjoint linear relation,
as a linear relation: the set of pairs `(C^{1/2} y, (1 − C)^{1/2} y)`, where
`C = (1 + T)⁻¹`. -/
noncomputable def sqrtRel (hT : IsNonnegSelfAdjoint T) : Submodule ℂ (F × F) :=
  LinearMap.range ((sqrtB hT).toLinearMap.prod (sqrtC hT).toLinearMap)

theorem mem_sqrtRel_iff {hT : IsNonnegSelfAdjoint T} {p : F × F} :
    p ∈ sqrtRel hT ↔ ∃ y, sqrtB hT y = p.1 ∧ sqrtC hT y = p.2 := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simp [← hy], by simp [← hy]⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨y, Prod.ext h1 h2⟩

theorem mem_sqrtRel (hT : IsNonnegSelfAdjoint T) (y : F) :
    (sqrtB hT y, sqrtC hT y) ∈ sqrtRel hT :=
  mem_sqrtRel_iff.2 ⟨y, rfl, rfl⟩

theorem sqrtB_mul_sqrtB (hT : IsNonnegSelfAdjoint T) : sqrtB hT * sqrtB hT = invCLM hT :=
  sqrtOp_mul_self (invCLM_nonneg hT) (invCLM_le_one hT)

theorem sqrtC_mul_sqrtC (hT : IsNonnegSelfAdjoint T) : sqrtC hT * sqrtC hT = 1 - invCLM hT :=
  coSqrtOp_mul_self (invCLM_nonneg hT) (invCLM_le_one hT)

theorem sqrtB_mul_sqrtC (hT : IsNonnegSelfAdjoint T) :
    sqrtB hT * sqrtC hT = midOp (invCLM hT) :=
  sqrtOp_mul_coSqrtOp (invCLM_nonneg hT)

theorem sqrtC_mul_sqrtB (hT : IsNonnegSelfAdjoint T) :
    sqrtC hT * sqrtB hT = midOp (invCLM hT) :=
  coSqrtOp_mul_sqrtOp (invCLM_nonneg hT)

theorem isSelfAdjoint_sqrtB (hT : IsNonnegSelfAdjoint T) : IsSelfAdjoint (sqrtB hT) :=
  isSelfAdjoint_sqrtOp _

theorem isSelfAdjoint_sqrtC (hT : IsNonnegSelfAdjoint T) : IsSelfAdjoint (sqrtC hT) :=
  isSelfAdjoint_coSqrtOp _

theorem sqrtB_sqrtB_apply (hT : IsNonnegSelfAdjoint T) (y : F) :
    sqrtB hT (sqrtB hT y) = invCLM hT y := by
  have h : (sqrtB hT * sqrtB hT) y = invCLM hT y := by rw [sqrtB_mul_sqrtB]
  exact h

theorem sqrtC_sqrtC_apply (hT : IsNonnegSelfAdjoint T) (y : F) :
    sqrtC hT (sqrtC hT y) = y - invCLM hT y := by
  have h : (sqrtC hT * sqrtC hT) y = ((1 : F →L[ℂ] F) - invCLM hT) y := by rw [sqrtC_mul_sqrtC]
  simpa using h

theorem sqrtB_sqrtC_apply (hT : IsNonnegSelfAdjoint T) (y : F) :
    sqrtB hT (sqrtC hT y) = sqrtC hT (sqrtB hT y) := by
  have h1 : (sqrtB hT * sqrtC hT) y = midOp (invCLM hT) y := by rw [sqrtB_mul_sqrtC]
  have h2 : (sqrtC hT * sqrtB hT) y = midOp (invCLM hT) y := by rw [sqrtC_mul_sqrtB]
  exact h1.trans h2.symm

/-! ## `T^{1/2}` is a non-negative self-adjoint relation -/

/-- **`T^{1/2}` is symmetric.** -/
theorem sqrtRel_le_adjPairs (hT : IsNonnegSelfAdjoint T) :
    sqrtRel hT ≤ adjPairs (sqrtRel hT) := by
  intro p hp q hq
  obtain ⟨y, hy1, hy2⟩ := mem_sqrtRel_iff.1 hp
  obtain ⟨z, hz1, hz2⟩ := mem_sqrtRel_iff.1 hq
  rw [← hy1, ← hy2, ← hz1, ← hz2,
    inner_isSelfAdjoint_left (isSelfAdjoint_sqrtC hT),
    inner_isSelfAdjoint_left (isSelfAdjoint_sqrtB hT), sqrtB_sqrtC_apply]

/-- **`1 + T^{1/2}` is surjective.** -/
theorem exists_mem_sqrtRel_add (hT : IsNonnegSelfAdjoint T) (h : F) :
    ∃ p ∈ sqrtRel hT, p.1 + p.2 = h := by
  obtain ⟨y, hy⟩ :=
    exists_sqrtOp_add_coSqrtOp_eq (invCLM_nonneg hT) (invCLM_le_one hT) h
  exact ⟨(sqrtB hT y, sqrtC hT y), mem_sqrtRel hT y, hy⟩

/-- **`T^{1/2}` is self-adjoint.** -/
theorem adjPairs_sqrtRel (hT : IsNonnegSelfAdjoint T) :
    adjPairs (sqrtRel hT) = sqrtRel hT :=
  adjPairs_eq_self_of_symmetric_of_surjective (sqrtRel_le_adjPairs hT)
    (exists_mem_sqrtRel_add hT)

/-- The graph of `T^{1/2}` is closed. -/
theorem sqrtRel_isClosed (hT : IsNonnegSelfAdjoint T) :
    IsClosed ((sqrtRel hT : Submodule ℂ (F × F)) : Set (F × F)) := by
  rw [← adjPairs_sqrtRel hT]
  exact adjPairs_isClosed _

/-- **`T^{1/2} ≥ 0`.** -/
theorem sqrtRel_quadForm_nonneg (hT : IsNonnegSelfAdjoint T) {p : F × F} (hp : p ∈ sqrtRel hT) :
    0 ≤ (inner ℂ p.2 p.1 : ℂ) := by
  obtain ⟨y, hy1, hy2⟩ := mem_sqrtRel_iff.1 hp
  have hpos : (midOp (invCLM hT)).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 (midOp_nonneg _)
  have hmid : sqrtC hT (sqrtB hT y) = midOp (invCLM hT) y := by
    have h : (sqrtC hT * sqrtB hT) y = midOp (invCLM hT) y := by rw [sqrtC_mul_sqrtB]
    exact h
  rw [← hy1, ← hy2, inner_isSelfAdjoint_left (isSelfAdjoint_sqrtC hT), hmid]
  exact hpos.inner_nonneg_right y

/-- **`T^{1/2}` is itself a non-negative self-adjoint relation.** -/
theorem isNonnegSelfAdjoint_sqrtRel (hT : IsNonnegSelfAdjoint T) :
    IsNonnegSelfAdjoint (sqrtRel hT) where
  adj := adjPairs_sqrtRel hT
  nonneg := by
    intro p hp
    have h := sqrtRel_quadForm_nonneg hT hp
    have hre : 0 ≤ (inner ℂ p.2 p.1 : ℂ).re := by
      have := Complex.le_def.1 h
      simpa using this.1
    have hconj : (inner ℂ p.2 p.1 : ℂ) = (starRingEnd ℂ) (inner ℂ p.1 p.2 : ℂ) :=
      (inner_conj_symm _ _).symm
    rwa [hconj, Complex.conj_re] at hre

/-! ## `(T^{1/2})² = T` -/

/-- **The square of `T^{1/2}` is `T`.** -/
theorem sqrtRel_comp_self (hT : IsNonnegSelfAdjoint T) :
    {p : F × F | ∃ w, (p.1, w) ∈ sqrtRel hT ∧ (w, p.2) ∈ sqrtRel hT} = (T : Set (F × F)) := by
  ext p
  obtain ⟨x, z⟩ := p
  constructor
  · rintro ⟨w, hw1, hw2⟩
    obtain ⟨y, hy1, hy2⟩ := mem_sqrtRel_iff.1 hw1
    obtain ⟨y', hy1', hy2'⟩ := mem_sqrtRel_iff.1 hw2
    simp only at hy1 hy2 hy1' hy2'
    have hCC : sqrtC hT (sqrtC hT y) = sqrtB hT z := by
      rw [hy2, ← hy1', ← sqrtB_sqrtC_apply, hy2']
    have hy : y = sqrtB hT (sqrtB hT y + z) := by
      have h1 : sqrtB hT (sqrtB hT y) + sqrtC hT (sqrtC hT y) = y := by
        rw [sqrtB_sqrtB_apply, sqrtC_sqrtC_apply]; abel
      rw [map_add, ← hCC, h1]
    have hx : x = invCLM hT (sqrtB hT y + z) := by
      rw [← hy1]
      conv_lhs => rw [hy]
      rw [sqrtB_sqrtB_apply]
    have hsum : sqrtB hT y + z - x = z := by rw [← hy1]; abel
    have hmem := invCLM_mem hT (sqrtB hT y + z)
    rw [← hx, hsum] at hmem
    exact hmem
  · intro hp
    have hRx : invCLM hT (x + z) = x :=
      invCLM_eq_of_mem hT (by simpa using hp)
    refine ⟨sqrtC hT (sqrtB hT (x + z)), ?_, ?_⟩
    · refine mem_sqrtRel_iff.2 ⟨sqrtB hT (x + z), ?_, rfl⟩
      rw [sqrtB_sqrtB_apply, hRx]
    · refine mem_sqrtRel_iff.2 ⟨sqrtC hT (x + z), ?_, ?_⟩
      · exact (sqrtB_sqrtC_apply hT (x + z)).symm ▸ rfl
      · have h1 : sqrtC hT (sqrtC hT (x + z)) = (x + z) - invCLM hT (x + z) :=
          sqrtC_sqrtC_apply hT (x + z)
        rw [h1, hRx]
        abel

/-! ## Uniqueness -/

/-- **The bounded identity.**  If `S S ⊆ T` then, with `C = (1 + S)⁻¹` and
`R = (1 + T)⁻¹`, `R (1 − 2C + 2C²) = C²`. -/
theorem invCLM_mul_den (hT : IsNonnegSelfAdjoint T) (hS : IsNonnegSelfAdjoint S)
    (hsq : ∀ p : F × F, (∃ w, (p.1, w) ∈ S ∧ (w, p.2) ∈ S) → p ∈ T) :
    invCLM hT * (1 - invCLM hS - invCLM hS + invCLM hS * invCLM hS + invCLM hS * invCLM hS)
      = invCLM hS * invCLM hS := by
  refine ContinuousLinearMap.ext fun h => ?_
  have h1 : (invCLM hS h, h - invCLM hS h) ∈ S := invCLM_mem hS h
  have h2 : (invCLM hS (invCLM hS h), invCLM hS h - invCLM hS (invCLM hS h)) ∈ S :=
    invCLM_mem hS (invCLM hS h)
  have h3 : (invCLM hS h - invCLM hS (invCLM hS h),
      (h - invCLM hS h) - (invCLM hS h - invCLM hS (invCLM hS h))) ∈ S := by
    have := S.sub_mem h1 h2
    simpa using this
  have h4 : (invCLM hS (invCLM hS h),
      (h - invCLM hS h) - (invCLM hS h - invCLM hS (invCLM hS h))) ∈ T :=
    hsq _ ⟨invCLM hS h - invCLM hS (invCLM hS h), h2, h3⟩
  have hval : invCLM hT (h - invCLM hS h - invCLM hS h + invCLM hS (invCLM hS h)
      + invCLM hS (invCLM hS h)) = invCLM hS (invCLM hS h) := by
    refine invCLM_eq_of_mem hT ?_
    have hrw : h - invCLM hS h - invCLM hS h + invCLM hS (invCLM hS h)
        + invCLM hS (invCLM hS h) - invCLM hS (invCLM hS h)
        = (h - invCLM hS h) - (invCLM hS h - invCLM hS (invCLM hS h)) := by abel
    rw [hrw]
    exact h4
  simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using hval

/-- With `S S ⊆ T`, the resolvent of `S` is `ψ` of the resolvent of `T`. -/
theorem invCLM_eq_cfc_of_sq (hT : IsNonnegSelfAdjoint T) (hS : IsNonnegSelfAdjoint S)
    (hsq : ∀ p : F × F, (∃ w, (p.1, w) ∈ S ∧ (w, p.2) ∈ S) → p ∈ T) :
    invCLM hS = cfc psiFun (invCLM hT) :=
  eq_cfc_psiFun (invCLM hS) (invCLM hT) (invCLM_nonneg hS) (invCLM_le_one hS)
    (invCLM_mul_den hT hS hsq)

/-- **Uniqueness of the non-negative self-adjoint square root.**  Every
non-negative self-adjoint relation whose square is contained in `T` is
`T^{1/2}`. -/
theorem eq_sqrtRel_of_isNonnegSelfAdjoint (hT : IsNonnegSelfAdjoint T)
    (hS : IsNonnegSelfAdjoint S)
    (hsq : ∀ p : F × F, (∃ w, (p.1, w) ∈ S ∧ (w, p.2) ∈ S) → p ∈ T) :
    S = sqrtRel hT := by
  have hroot : ∀ p : F × F,
      (∃ w, (p.1, w) ∈ sqrtRel hT ∧ (w, p.2) ∈ sqrtRel hT) → p ∈ T := by
    intro p hp
    have hmem : p ∈ {q : F × F | ∃ w, (q.1, w) ∈ sqrtRel hT ∧ (w, q.2) ∈ sqrtRel hT} := hp
    rw [sqrtRel_comp_self hT] at hmem
    exact hmem
  exact rel_eq_of_invCLM_eq hS (isNonnegSelfAdjoint_sqrtRel hT)
    ((invCLM_eq_cfc_of_sq hT hS hsq).trans
      (invCLM_eq_cfc_of_sq hT (isNonnegSelfAdjoint_sqrtRel hT) hroot).symm)

/-- **Every non-negative self-adjoint linear relation has a unique non-negative
self-adjoint square root.** -/
theorem sqrtRel_unique_nonneg_sqrt (hT : IsNonnegSelfAdjoint T) :
    IsNonnegSelfAdjoint (sqrtRel hT) ∧
      {p : F × F | ∃ w, (p.1, w) ∈ sqrtRel hT ∧ (w, p.2) ∈ sqrtRel hT} = (T : Set (F × F)) ∧
      ∀ S : Submodule ℂ (F × F), IsNonnegSelfAdjoint S →
        {p : F × F | ∃ w, (p.1, w) ∈ S ∧ (w, p.2) ∈ S} = (T : Set (F × F)) →
        S = sqrtRel hT := by
  refine ⟨isNonnegSelfAdjoint_sqrtRel hT, sqrtRel_comp_self hT, fun S hS hsq => ?_⟩
  refine eq_sqrtRel_of_isNonnegSelfAdjoint hT hS fun p hp => ?_
  have hmem : p ∈ {q : F × F | ∃ w, (q.1, w) ∈ S ∧ (w, q.2) ∈ S} := hp
  rw [hsq] at hmem
  exact hmem

/-! ## Single-valuedness is inherited -/

/-- If `T` is single-valued (an operator), then `(1 + T)⁻¹` is injective. -/
theorem invCLM_injective (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) : Function.Injective (invCLM hT) := by
  intro a b hab
  have h0 : invCLM hT (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hmem := invCLM_mem hT (a - b)
  rw [h0] at hmem
  have := hsv _ (by simpa using hmem)
  exact sub_eq_zero.1 this

/-- **If `T` is an operator, so is `T^{1/2}`.** -/
theorem sqrtRel_snd_eq_zero_of_fst_eq_zero (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {w : F} (h : ((0 : F), w) ∈ sqrtRel hT) :
    w = 0 := by
  obtain ⟨y, hy1, hy2⟩ := mem_sqrtRel_iff.1 h
  simp only at hy1 hy2
  have hy0 : y = 0 :=
    sqrtOp_injective (invCLM_nonneg hT) (invCLM_le_one hT) (invCLM_injective hT hsv)
      (by simpa [sqrtB] using hy1)
  rw [← hy2, hy0, map_zero]

/-! ## The form of `T`: `⟪x, T x⟫ = ‖T^{1/2} x‖²` -/

/-- **`D(T) ⊆ D(T^{1/2})`**: every point of the domain of `T` lies in the domain of
its square root. -/
theorem exists_mem_sqrtRel_of_mem (hT : IsNonnegSelfAdjoint T) {p : F × F} (hp : p ∈ T) :
    ∃ w, (p.1, w) ∈ sqrtRel hT := by
  have hx : invCLM hT (p.1 + p.2) = p.1 := invCLM_eq_of_mem hT (by simpa using hp)
  refine ⟨sqrtC hT (sqrtB hT (p.1 + p.2)), mem_sqrtRel_iff.2 ⟨sqrtB hT (p.1 + p.2), ?_, rfl⟩⟩
  rw [sqrtB_sqrtB_apply, hx]

/-- **The form identity `⟪x, T x⟫ = ‖T^{1/2} x‖²`**, for `T` single-valued (an
operator), in which case `T^{1/2}` is single-valued too. -/
theorem inner_eq_norm_sq_of_mem (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ v : F, ((0 : F), v) ∈ T → v = 0) {x z w : F} (hz : (x, z) ∈ T)
    (hw : (x, w) ∈ sqrtRel hT) : (inner ℂ x z : ℂ) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  set h : F := x + z with hh
  have hx : invCLM hT h = x := invCLM_eq_of_mem hT (by simpa [hh] using hz)
  obtain ⟨y, hy1, hy2⟩ := mem_sqrtRel_iff.1 hw
  simp only at hy1 hy2
  have hBinj : Function.Injective (sqrtB hT) :=
    sqrtOp_injective (invCLM_nonneg hT) (invCLM_le_one hT) (invCLM_injective hT hsv)
  have hBh : sqrtB hT (sqrtB hT h) = x := by rw [sqrtB_sqrtB_apply, hx]
  have hy : y = sqrtB hT h := hBinj (by rw [hy1, hBh])
  have hwval : w = sqrtC hT (sqrtB hT h) := by rw [← hy2, hy]
  have e0 : (inner ℂ w w : ℂ)
      = inner ℂ (sqrtC hT (sqrtC hT (sqrtB hT h))) (sqrtB hT h) := by
    rw [hwval,
      inner_isSelfAdjoint_left (isSelfAdjoint_sqrtC hT) (sqrtC hT (sqrtB hT h)) (sqrtB hT h)]
  have e1 : (inner ℂ (sqrtB hT h) (sqrtB hT h) : ℂ) = inner ℂ x h := by
    rw [← hBh, inner_isSelfAdjoint_left (isSelfAdjoint_sqrtB hT) (sqrtB hT h) h]
  have e2 : (inner ℂ (invCLM hT (sqrtB hT h)) (sqrtB hT h) : ℂ) = inner ℂ x x := by
    rw [← sqrtB_sqrtB_apply, ← hBh,
      inner_isSelfAdjoint_left (isSelfAdjoint_sqrtB hT) (sqrtB hT (sqrtB hT h)) (sqrtB hT h)]
  have e3 : (inner ℂ w w : ℂ) = inner ℂ x h - inner ℂ x x := by
    rw [e0, sqrtC_sqrtC_apply, inner_sub_left, e1, e2]
  have e4 : (inner ℂ x z : ℂ) = inner ℂ x h - inner ℂ x x := by
    rw [hh, inner_add_right]; ring
  have hww : (inner ℂ w w : ℂ) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [e4, ← e3, hww]

/-- **The quadratic form of `T` is the squared norm of `T^{1/2}`.**  In particular
it is non-negative, and `‖T^{1/2} x‖` is determined by `x`. -/
theorem norm_sq_eq_inner_of_mem (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ v : F, ((0 : F), v) ∈ T → v = 0) {x z w : F} (hz : (x, z) ∈ T)
    (hw : (x, w) ∈ sqrtRel hT) : ‖w‖ ^ 2 = (inner ℂ x z : ℂ).re := by
  rw [inner_eq_norm_sq_of_mem hT hsv hz hw, Complex.ofReal_re]

/-! ## Commutation -/

/-- A bounded operator commuting with the resolvent of `T` leaves `T` invariant. -/
theorem mem_of_commute (hT : IsNonnegSelfAdjoint T) {B : F →L[ℂ] F}
    (hB : Commute (invCLM hT) B) {p : F × F} (hp : p ∈ T) : (B p.1, B p.2) ∈ T := by
  have hx : invCLM hT (p.1 + p.2) = p.1 := invCLM_eq_of_mem hT (by simpa using hp)
  have hBx : invCLM hT (B p.1 + B p.2) = B p.1 := by
    have hcomm : (invCLM hT * B) (p.1 + p.2) = (B * invCLM hT) (p.1 + p.2) := by rw [hB]
    simp only [ContinuousLinearMap.mul_apply] at hcomm
    rw [← map_add, hcomm, hx]
  have hmem := invCLM_mem hT (B p.1 + B p.2)
  rw [hBx] at hmem
  simpa using hmem

/-- **A bounded operator commuting with the resolvent of `T` commutes with `T^{1/2}`**:
it maps the square root relation into itself. -/
theorem mem_sqrtRel_of_commute (hT : IsNonnegSelfAdjoint T) {B : F →L[ℂ] F}
    (hB : Commute (invCLM hT) B) {p : F × F} (hp : p ∈ sqrtRel hT) :
    (B p.1, B p.2) ∈ sqrtRel hT := by
  obtain ⟨y, hy1, hy2⟩ := mem_sqrtRel_iff.1 hp
  have hsa : IsSelfAdjoint (invCLM hT) := (invCLM_nonneg hT).isSelfAdjoint
  have h1 : Commute (sqrtB hT) B := hsa.commute_cfc (𝕜 := ℝ) hB Real.sqrt
  have h2 : Commute (sqrtC hT) B := hsa.commute_cfc (𝕜 := ℝ) hB fun t => Real.sqrt (1 - t)
  refine mem_sqrtRel_iff.2 ⟨B y, ?_, ?_⟩
  · have := congrArg (fun S : F →L[ℂ] F => S y) h1
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [this, hy1]
  · have := congrArg (fun S : F →L[ℂ] F => S y) h2
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [this, hy2]

/-! ## The resolvent at every negative real: `T + a` is boundedly invertible for `a > 0` -/

/-- Scaling of the second coordinate, `(x, z) ↦ (x, c z)`. -/
def smulSnd (c : ℝ) : (F × F) →ₗ[ℂ] (F × F) :=
  (LinearMap.fst ℂ F F).prod ((c : ℂ) • LinearMap.snd ℂ F F)

omit [CompleteSpace F] in
@[simp] theorem smulSnd_apply (c : ℝ) (p : F × F) : smulSnd c p = (p.1, (c : ℂ) • p.2) := rfl

/-- The scaled relation `c T = {(x, c z) : (x, z) ∈ T}`, for a real scalar `c`. -/
def smulRel (c : ℝ) (T : Submodule ℂ (F × F)) : Submodule ℂ (F × F) := T.map (smulSnd c)

omit [CompleteSpace F] in
theorem mem_smulRel_iff {c : ℝ} (hc : c ≠ 0) {p : F × F} :
    p ∈ smulRel c T ↔ (p.1, ((c : ℂ))⁻¹ • p.2) ∈ T := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  constructor
  · rintro ⟨q, hq, rfl⟩
    simp only [smulSnd_apply, smul_smul, inv_mul_cancel₀ hc', one_smul]
    exact hq
  · intro hp
    refine ⟨(p.1, ((c : ℂ))⁻¹ • p.2), hp, ?_⟩
    simp [smul_smul, mul_inv_cancel₀ hc']

omit [CompleteSpace F] in
theorem mem_smulRel {c : ℝ} {p : F × F} (hp : p ∈ T) : (p.1, (c : ℂ) • p.2) ∈ smulRel c T :=
  ⟨p, hp, rfl⟩

omit [CompleteSpace F] in
/-- The adjoint of a real multiple of a relation is that multiple of the adjoint. -/
theorem adjPairs_smulRel {c : ℝ} (hc : c ≠ 0) :
    adjPairs (smulRel c T) = smulRel c (adjPairs T) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  ext p
  rw [mem_smulRel_iff hc]
  constructor
  · intro hp q hq
    have h := hp _ (mem_smulRel (c := c) hq)
    simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h ⊢
    field_simp at h ⊢
    linear_combination h
  · intro hp q hq
    obtain ⟨r, hr, rfl⟩ := hq
    have h := hp r hr
    simp only [smulSnd_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h ⊢
    field_simp at h ⊢
    linear_combination h

omit [CompleteSpace F] in
/-- A positive multiple of a non-negative self-adjoint relation is again one. -/
theorem isNonnegSelfAdjoint_smulRel (hT : IsNonnegSelfAdjoint T) {c : ℝ} (hc : 0 < c) :
    IsNonnegSelfAdjoint (smulRel c T) where
  adj := by rw [adjPairs_smulRel hc.ne', hT.adj]
  nonneg := by
    rintro p ⟨q, hq, rfl⟩
    have h := hT.nonneg q hq
    simp only [smulSnd_apply, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    positivity

section Shift

variable {a : ℝ}

omit [CompleteSpace F] in
/-- The non-negative self-adjoint relation `a⁻¹ T`, whose resolvent computes that of
`T + a`. -/
theorem isNonnegSelfAdjoint_invSmulRel (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) :
    IsNonnegSelfAdjoint (smulRel a⁻¹ T) :=
  isNonnegSelfAdjoint_smulRel hT (inv_pos.2 ha)

/-- **`(T + a)⁻¹` for `a > 0`**, an everywhere-defined bounded operator. -/
noncomputable def invCLMAt (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) : F →L[ℂ] F :=
  ((a : ℂ))⁻¹ • invCLM (isNonnegSelfAdjoint_invSmulRel hT ha)

theorem invCLMAt_apply (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (h : F) :
    invCLMAt hT ha h = invCLM (isNonnegSelfAdjoint_invSmulRel hT ha) (((a : ℂ))⁻¹ • h) := by
  rw [invCLMAt, ContinuousLinearMap.smul_apply, map_smul]

/-- `(T + a)⁻¹ h` solves `a x + T x = h`. -/
theorem invCLMAt_mem (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (h : F) :
    (invCLMAt hT ha h, h - (a : ℂ) • invCLMAt hT ha h) ∈ T := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hinv : ((a⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simpa using (inv_ne_zero ha')
  have hmem := invCLM_mem (isNonnegSelfAdjoint_invSmulRel hT ha) (((a : ℂ))⁻¹ • h)
  rw [mem_smulRel_iff (inv_ne_zero ha.ne')] at hmem
  have hcast : (((a⁻¹ : ℝ) : ℂ))⁻¹ = (a : ℂ) := by
    push_cast
    rw [inv_inv]
  rw [hcast] at hmem
  rw [invCLMAt_apply]
  convert hmem using 2
  rw [smul_sub, smul_smul, mul_inv_cancel₀ ha', one_smul]

/-- Uniqueness: `a x + T x = h` has at most one solution. -/
theorem invCLMAt_eq_of_mem (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) {x h : F}
    (hx : (x, h - (a : ℂ) • x) ∈ T) : invCLMAt hT ha h = x := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hmem : (x, ((a : ℂ))⁻¹ • h - x) ∈ smulRel a⁻¹ T := by
    rw [mem_smulRel_iff (inv_ne_zero ha.ne')]
    have hcast : (((a⁻¹ : ℝ) : ℂ))⁻¹ = (a : ℂ) := by
      push_cast
      rw [inv_inv]
    rw [hcast]
    convert hx using 2
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ha', one_smul]
  rw [invCLMAt_apply]
  exact invCLM_eq_of_mem _ hmem

/-- **`‖(T + a)⁻¹‖ ≤ 1/a`.** -/
theorem norm_invCLMAt_le (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (h : F) :
    ‖invCLMAt hT ha h‖ ≤ a⁻¹ * ‖h‖ := by
  have hb := norm_invLin_le (isNonnegSelfAdjoint_invSmulRel hT ha) (((a : ℂ))⁻¹ • h)
  have hnorm : ‖((a : ℂ))⁻¹ • h‖ = a⁻¹ * ‖h‖ := by
    rw [norm_smul]
    simp [abs_of_pos ha]
  rw [invCLMAt_apply]
  calc ‖invCLM (isNonnegSelfAdjoint_invSmulRel hT ha) (((a : ℂ))⁻¹ • h)‖
      ≤ ‖((a : ℂ))⁻¹ • h‖ := hb
    _ = a⁻¹ * ‖h‖ := hnorm

/-- **The spectrum of a non-negative self-adjoint relation misses the negative reals.**
For every `a > 0` the equation `a x + T x = h` has exactly one solution, and it
depends on `h` boundedly with constant `1/a`. -/
theorem existsUnique_smul_add_mem (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (h : F) :
    ∃! x : F, (x, h - (a : ℂ) • x) ∈ T :=
  ⟨invCLMAt hT ha h, invCLMAt_mem hT ha h, fun x hx => by
    rw [← invCLMAt_eq_of_mem hT ha hx]⟩

end Shift

/-! ## The earlier `|Ā|` is `(A* Ā)^{1/2}` in this sense -/

variable {D : Submodule ℂ F}

/-- `A* Ā` is a non-negative self-adjoint linear relation. -/
theorem isNonnegSelfAdjoint_factorRel (A : D →ₗ[ℂ] F) : IsNonnegSelfAdjoint (factorRel A) where
  adj := adjPairs_factorRel A
  nonneg := by
    intro p hp
    obtain ⟨y, -, hval⟩ := inner_fst_add_self hp
    have h1 : (inner ℂ p.1 p.1 : ℂ) = ((‖p.1‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have h2 : (inner ℂ p.1 p.2 : ℂ) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
      have hsplit := hval
      rw [inner_add_right, h1] at hsplit
      push_cast at hsplit ⊢
      linear_combination hsplit
    rw [h2, Complex.ofReal_re]
    positivity

/-- **`|Ā|` is the square root of `A* Ā`** in the sense of `sqrtRel`. -/
theorem absRel_eq_sqrtRel (A : D →ₗ[ℂ] F) :
    absRel A = sqrtRel (isNonnegSelfAdjoint_factorRel A) := by
  refine eq_sqrtRel_of_isNonnegSelfAdjoint _ (isNonnegSelfAdjoint_absRel A) fun p hp => ?_
  have hmem : p ∈ {q : F × F | ∃ w, (q.1, w) ∈ absRel A ∧ (w, q.2) ∈ absRel A} := hp
  rw [absRel_comp_self A] at hmem
  exact hmem

end BookProof.NonnegSquareRoot


