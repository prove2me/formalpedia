-- Prove2me | Definitions.Def_ChapterUnboundedPolar
-- name    : ChapterUnboundedPolar
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T12:07:43.892871+00:00
-- url     : https://prove2.me/theorems/be51d96f-6800-438e-a2e7-4bbfd7797767
-- title:
--   The unbounded polar decomposition: `|Ā| = (A* Ā)^{1/2}` and `Ā = U |Ā|`
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.UnboundedPolar`, source chapter `BookProof/ChapterUnboundedPolar.lean`): The unbounded polar decomposition: `|Ā| = (A* Ā)^{1/2}` and `Ā = U |Ā|`
--
--   This bundle proves the positive square root `|Ā| = (A* Ā)^{1/2}` of the unbounded operator `A* Ā` and the polar decomposition `Ā = U |Ā|`, using the bounded continuous functional calculus applied to the positive contraction `R = (1 + A* Ā)⁻¹` — no unbounded functional calculus is needed. Source chapter `BookProof/ChapterUnboundedPolar.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPolar.lean

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosure
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterVonNeumannCore
import Theorems.Thm_BookProof_FriedrichsSquare_coe_factorRel
import Theorems.Thm_BookProof_ClosureUniqueness_exists_linearIsometry_of_inner_eq


/-!
# The unbounded polar decomposition: `|Ā| = (A* Ā)^{1/2}` and `Ā = U |Ā|`

`BookProof.ChapterFriedrichsSquareFactorization` builds the composite `A* Ā` as a
linear relation `factorRel A` and proves it self-adjoint;
`BookProof.ChapterVonNeumannCore` adds the bounded inverse
`R = (1 + A* Ā)⁻¹ = resCLM A` and von Neumann's core theorem.  Both modules
recorded the same boundary: the *positive square root* `|Ā| = (A* Ā)^{1/2}` of
the unbounded operator `A* Ā`, and the polar decomposition `Ā = U |Ā|`, were not
proved, because they appear to need a functional calculus for unbounded
self-adjoint operators.

This module proves them, without any unbounded functional calculus.  The whole
construction is carried out with the **bounded** continuous functional calculus
applied to the single positive contraction `R = (1 + A* Ā)⁻¹`:

* `sqrtOp R = R^{1/2}` and `coSqrtOp R = (1 − R)^{1/2}`;
* `|Ā|` is the linear relation `absRel A = {(R^{1/2} y, (1 − R)^{1/2} y) : y}`.

Formally `|Ā| = (1 − R)^{1/2} R^{−1/2}`, which is `((R⁻¹ − 1))^{1/2} = (A* Ā)^{1/2}`,
and its domain is the range of `R^{1/2}`.

## What is proved

Part 0 — a general criterion, extracted from von Neumann's argument: a symmetric
linear relation `S` with `1 + S` surjective is self-adjoint
(`adjPairs_eq_self_of_symmetric_of_surjective`).

Part 1 — the bounded square roots of a positive contraction `R`: `sqrtOp`,
`coSqrtOp`, `midOp` with `R^{1/2} R^{1/2} = R`, `(1−R)^{1/2}(1−R)^{1/2} = 1 − R`,
the commutation `R^{1/2}(1−R)^{1/2} = (1−R)^{1/2}R^{1/2} = midOp R`, positivity,
and the invertibility of `R^{1/2} + (1 − R)^{1/2}` (its spectrum lies in `[1, √2]`).

Part 2 — `R = resCLM A` is a positive, injective contraction (`resCLM_nonneg`,
`resCLM_le_one`, `resCLM_injective`).

Part 3 — the absolute value `absRel A`: it is single-valued, symmetric, positive,
`1 + |Ā|` is surjective, hence **`|Ā|` is self-adjoint** (`adjPairs_absRel`), and
**`|Ā|² = A* Ā`** (`absRel_comp_self`).

Part 4 — the domain and the norm: `D(|Ā|) = D(Ā)` and `‖ |Ā| x ‖ = ‖Ā x‖`
(`absDom_eq_clDom`, `norm_absFun_eq`), proved from von Neumann's core theorem
applied on both sides.

Part 5 — **the polar decomposition** `Ā = U |Ā|`, with `U` a linear isometry of
`ran |Ā|` onto `ran Ā` (`exists_polar_isometry`).

Hypotheses: `F` is a complex Hilbert space, `A` is symmetric on a dense domain
`D`.  No invariance of the domain is used.
-/

namespace BookProof.UnboundedPolar

open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.FriedrichsSquare BookProof.VonNeumannCore
open scoped ComplexOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## Part 0 — a symmetric relation with `1 + S` surjective is self-adjoint -/

/-- **Self-adjointness criterion for linear relations.**  If a linear relation
`S ⊆ F × F` is symmetric (`S ⊆ S*`) and `1 + S` is surjective, then `S* = S`.
This is the step of von Neumann's theorem that upgrades symmetry to
self-adjointness. -/
theorem adjPairs_eq_self_of_symmetric_of_surjective {S : Submodule ℂ (F × F)}
    (hsym : S ≤ adjPairs S) (hsurj : ∀ h : F, ∃ p ∈ S, p.1 + p.2 = h) :
    adjPairs S = S := by
  refine le_antisymm ?_ hsym
  intro p hp
  obtain ⟨r, hr, hrsum⟩ := hsurj (p.1 + p.2)
  have hv : p - r ∈ adjPairs S := (adjPairs S).sub_mem hp (hsym hr)
  have hvsum : (p - r).1 + (p - r).2 = 0 := by
    have hsplit : (p - r).1 + (p - r).2 = (p.1 + p.2) - (r.1 + r.2) := by
      simp only [Prod.fst_sub, Prod.snd_sub]; abel
    rw [hsplit, hrsum, sub_self]
  have key : ∀ x : F, (inner ℂ x (p - r).1 : ℂ) = 0 := by
    intro x
    obtain ⟨q, hq, hqsum⟩ := hsurj x
    have hqv := hv q hq
    have hzero : (inner ℂ q.1 ((p - r).1 + (p - r).2) : ℂ) = 0 := by rw [hvsum]; simp
    rw [inner_add_right] at hzero
    rw [← hqsum, inner_add_left, hqv]
    linear_combination hzero
  have hv1 : (p - r).1 = 0 := inner_self_eq_zero.1 (key (p - r).1)
  have hv2 : (p - r).2 = 0 := by
    have := hvsum; rw [hv1, zero_add] at this; exact this
  have hpr : p = r := by
    refine Prod.ext ?_ ?_
    · have := hv1; simp only [Prod.fst_sub, sub_eq_zero] at this; exact this
    · have := hv2; simp only [Prod.snd_sub, sub_eq_zero] at this; exact this
  rw [hpr]; exact hr

/-- The adjoint of a relation is a closed subspace. -/
theorem adjPairs_isClosed (S : Submodule ℂ (F × F)) :
    IsClosed ((adjPairs S : Submodule ℂ (F × F)) : Set (F × F)) := by
  have : ((adjPairs S : Submodule ℂ (F × F)) : Set (F × F))
      = ⋂ q ∈ (S : Set (F × F)), {p : F × F | (inner ℂ q.2 p.1 : ℂ) = inner ℂ q.1 p.2} := by
    ext p; simp only [Set.mem_iInter, Set.mem_setOf_eq]; rfl
  rw [this]
  refine isClosed_biInter fun q _ => ?_
  exact isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)

/-! ## Part 1 — the bounded square roots of a positive contraction -/

section Sqrt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `R^{1/2}` for a positive contraction `R`. -/
noncomputable def sqrtOp (R : H →L[ℂ] H) : H →L[ℂ] H := cfc Real.sqrt R

/-- `(1 − R)^{1/2}` for a positive contraction `R`. -/
noncomputable def coSqrtOp (R : H →L[ℂ] H) : H →L[ℂ] H := cfc (fun t => Real.sqrt (1 - t)) R

/-- `R^{1/2} (1 − R)^{1/2}`. -/
noncomputable def midOp (R : H →L[ℂ] H) : H →L[ℂ] H :=
  cfc (fun t => Real.sqrt t * Real.sqrt (1 - t)) R

variable {R : H →L[ℂ] H}

/-- The spectrum of a positive contraction lies in `[0, 1]`. -/
theorem spectrum_subset_Icc (hR : 0 ≤ R) (h1 : R ≤ 1) : spectrum ℝ R ⊆ Set.Icc 0 1 := by
  intro t ht
  exact ⟨spectrum_nonneg_of_nonneg hR ht,
    (le_algebraMap_iff_spectrum_le (R := ℝ) (a := R) (r := 1)).1 (by simpa using h1) t ht⟩

theorem sqrtOp_mul_self (hR : 0 ≤ R) (h1 : R ≤ 1) : sqrtOp R * sqrtOp R = R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  have hs := spectrum_subset_Icc hR h1
  rw [sqrtOp, ← cfc_mul (R := ℝ) Real.sqrt Real.sqrt R]
  have h : cfc (fun x => Real.sqrt x * Real.sqrt x) R = cfc (id : ℝ → ℝ) R :=
    cfc_congr fun x hx => by simp [Real.mul_self_sqrt (hs hx).1]
  rw [h, cfc_id ℝ R]

theorem coSqrtOp_mul_self (hR : 0 ≤ R) (h1 : R ≤ 1) : coSqrtOp R * coSqrtOp R = 1 - R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  have hs := spectrum_subset_Icc hR h1
  rw [coSqrtOp, ← cfc_mul (R := ℝ) _ _ R]
  have h : cfc (fun x => Real.sqrt (1 - x) * Real.sqrt (1 - x)) R
      = cfc (fun x : ℝ => 1 - id x) R :=
    cfc_congr fun x hx => by
      have hx' : (0:ℝ) ≤ 1 - x := by have := (hs hx).2; linarith
      simp [Real.mul_self_sqrt hx']
  rw [h, cfc_sub (R := ℝ) (fun _ => (1:ℝ)) id R, cfc_const_one ℝ R, cfc_id ℝ R]

theorem sqrtOp_mul_coSqrtOp (hR : 0 ≤ R) :
    sqrtOp R * coSqrtOp R = midOp R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  rw [sqrtOp, coSqrtOp, midOp, cfc_mul (R := ℝ) _ _ R]

theorem coSqrtOp_mul_sqrtOp (hR : 0 ≤ R) :
    coSqrtOp R * sqrtOp R = midOp R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  rw [sqrtOp, coSqrtOp, midOp, cfc_mul (R := ℝ) _ _ R]
  have h : cfc (fun x => Real.sqrt (1 - x) * Real.sqrt x) R
      = cfc (fun x => Real.sqrt x * Real.sqrt (1 - x)) R :=
    cfc_congr fun x _ => mul_comm _ _
  rw [← cfc_mul (R := ℝ) _ _ R, h, cfc_mul (R := ℝ) _ _ R]

theorem sqrtOp_nonneg (R : H →L[ℂ] H) : 0 ≤ sqrtOp R :=
  cfc_nonneg fun x _ => Real.sqrt_nonneg x

theorem coSqrtOp_nonneg (R : H →L[ℂ] H) : 0 ≤ coSqrtOp R :=
  cfc_nonneg fun _ _ => Real.sqrt_nonneg _

theorem midOp_nonneg (R : H →L[ℂ] H) : 0 ≤ midOp R :=
  cfc_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem isSelfAdjoint_sqrtOp (R : H →L[ℂ] H) : IsSelfAdjoint (sqrtOp R) :=
  (sqrtOp_nonneg R).isSelfAdjoint

theorem isSelfAdjoint_coSqrtOp (R : H →L[ℂ] H) : IsSelfAdjoint (coSqrtOp R) :=
  (coSqrtOp_nonneg R).isSelfAdjoint

/-- `R^{1/2} + (1 − R)^{1/2} ≥ 1`: on the spectrum, `√t + √(1−t) ≥ 1`. -/
theorem one_le_sqrtOp_add_coSqrtOp (hR : 0 ≤ R) (h1 : R ≤ 1) :
    1 ≤ sqrtOp R + coSqrtOp R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  have hs := spectrum_subset_Icc hR h1
  have h : sqrtOp R + coSqrtOp R = cfc (fun t => Real.sqrt t + Real.sqrt (1 - t)) R := by
    rw [sqrtOp, coSqrtOp, cfc_add R _ _]
  rw [h]
  refine one_le_cfc _ _ fun x hx => ?_
  obtain ⟨hx0, hx1⟩ := hs hx
  nlinarith [Real.sq_sqrt hx0, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - x),
    Real.sqrt_nonneg x, Real.sqrt_nonneg (1 - x)]

/-- Hence `R^{1/2} + (1 − R)^{1/2}` is invertible. -/
theorem isUnit_sqrtOp_add_coSqrtOp (hR : 0 ≤ R) (h1 : R ≤ 1) :
    IsUnit (sqrtOp R + coSqrtOp R) := by
  have hsa : IsSelfAdjoint (sqrtOp R + coSqrtOp R) :=
    (isSelfAdjoint_sqrtOp R).add (isSelfAdjoint_coSqrtOp R)
  have hle : ∀ x ∈ spectrum ℝ (sqrtOp R + coSqrtOp R), (1:ℝ) ≤ x :=
    (algebraMap_le_iff_le_spectrum (R := ℝ) (a := sqrtOp R + coSqrtOp R) (r := 1)).1
      (by simpa using one_le_sqrtOp_add_coSqrtOp hR h1)
  refine (spectrum.zero_notMem_iff ℝ).1 fun h0 => ?_
  have := hle 0 h0
  linarith

/-- `R^{1/2} + (1 − R)^{1/2}` is surjective. -/
theorem exists_sqrtOp_add_coSqrtOp_eq (hR : 0 ≤ R) (h1 : R ≤ 1) (h : H) :
    ∃ y : H, sqrtOp R y + coSqrtOp R y = h := by
  obtain ⟨u, hu⟩ := isUnit_sqrtOp_add_coSqrtOp hR h1
  refine ⟨(↑u⁻¹ : H →L[ℂ] H) h, ?_⟩
  have : (sqrtOp R + coSqrtOp R) ((↑u⁻¹ : H →L[ℂ] H) h) = h := by
    have hmul : (sqrtOp R + coSqrtOp R) * (↑u⁻¹ : H →L[ℂ] H) = 1 := by
      rw [← hu]; exact u.mul_inv
    calc (sqrtOp R + coSqrtOp R) ((↑u⁻¹ : H →L[ℂ] H) h)
        = ((sqrtOp R + coSqrtOp R) * (↑u⁻¹ : H →L[ℂ] H)) h := rfl
      _ = h := by rw [hmul]; rfl
  simpa using this

/-- `R^{1/2}` is injective when `R` is. -/
theorem sqrtOp_injective (hR : 0 ≤ R) (h1 : R ≤ 1) (hinj : Function.Injective R) :
    Function.Injective (sqrtOp R) := by
  intro y z hyz
  refine hinj ?_
  have h2 : (sqrtOp R * sqrtOp R) y = (sqrtOp R * sqrtOp R) z := by
    change sqrtOp R (sqrtOp R y) = sqrtOp R (sqrtOp R z); rw [hyz]
  rwa [sqrtOp_mul_self hR h1] at h2

end Sqrt

/-- For a self-adjoint bounded operator the inner product may be moved across. -/
theorem inner_isSelfAdjoint_left [CompleteSpace F] {T : F →L[ℂ] F} (hT : IsSelfAdjoint T)
    (x y : F) : (inner ℂ (T x) y : ℂ) = inner ℂ x (T y) := by
  conv_lhs => rw [← hT.star_eq, ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_left]

/-! ## Part 2 — the resolvent is a positive injective contraction -/

section Resolvent

variable [CompleteSpace F] {D : Submodule ℂ F}

/-- The quadratic form of the resolvent: `⟪Rh, h⟫ = ‖Rh‖² + ‖Ā Rh‖² ≤ ‖h‖²`. -/
theorem inner_resCLM_self (A : D →ₗ[ℂ] F) (h : F) :
    ∃ y : F, (resCLM A h, y) ∈ clGraph A ∧
      (inner ℂ (resCLM A h) h : ℂ) = ((‖resCLM A h‖ ^ 2 + ‖y‖ ^ 2 : ℝ) : ℂ) ∧
      ‖resCLM A h‖ ^ 2 + ‖y‖ ^ 2 ≤ ‖h‖ ^ 2 := by
  have hmem := resLin_mem_factorRel A h
  obtain ⟨y, hy, hval⟩ := inner_fst_add_self hmem
  simp only at hy hval
  have hsum : resLin A h + (h - resLin A h) = h := by abel
  rw [hsum] at hval
  have hle : ‖resLin A h‖ ≤ ‖h‖ := norm_resLin_le A h
  have hre : ‖resLin A h‖ ^ 2 + ‖y‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    have h1 : (inner ℂ (resLin A h) h : ℂ).re = ‖resLin A h‖ ^ 2 + ‖y‖ ^ 2 := by
      rw [hval, Complex.ofReal_re]
    have h2 : (inner ℂ (resLin A h) h : ℂ).re ≤ ‖resLin A h‖ * ‖h‖ := by
      simpa using re_inner_le_norm (𝕜 := ℂ) (resLin A h) h
    rw [h1] at h2
    nlinarith [norm_nonneg (resLin A h), norm_nonneg h]
  exact ⟨y, hy, hval, hre⟩

/-- **`(1 + A* Ā)⁻¹ ≥ 0`.** -/
theorem resCLM_nonneg (A : D →ₗ[ℂ] F) : 0 ≤ resCLM A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  obtain ⟨y, -, hval, -⟩ := inner_resCLM_self A x
  rw [hval]
  refine ⟨by simp only [RCLike.re_to_complex, Complex.ofReal_re], ?_⟩
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  positivity

/-- **`(1 + A* Ā)⁻¹ ≤ 1`.** -/
theorem resCLM_le_one (A : D →ₗ[ℂ] F) : resCLM A ≤ 1 := by
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro x
  obtain ⟨y, -, hval, hbd⟩ := inner_resCLM_self A x
  have happ : ((1 : F →L[ℂ] F) - resCLM A) x = x - resCLM A x := rfl
  have hx : (inner ℂ x x : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hkey : (inner ℂ (((1 : F →L[ℂ] F) - resCLM A) x) x : ℂ)
      = (((‖x‖ ^ 2 - (‖resCLM A x‖ ^ 2 + ‖y‖ ^ 2) : ℝ)) : ℂ) := by
    rw [happ, inner_sub_left, hx, hval, ← Complex.ofReal_sub]
  rw [hkey]
  refine ⟨by simp only [RCLike.re_to_complex, Complex.ofReal_re], ?_⟩
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  linarith

/-- **`(1 + A* Ā)⁻¹` is injective.** -/
theorem resCLM_injective (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    Function.Injective (resCLM A) := by
  intro a b hab
  have hzero : resLin A (a - b) = 0 := by
    have : resCLM A (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    simpa [resCLM_apply] using this
  have hmem := resLin_mem_factorRel A (a - b)
  rw [hzero] at hmem
  have h0 : ((0 : F), a - b) ∈ factorRel A := by simpa using hmem
  have := factorRel_snd_eq_zero_of_fst_eq_zero hdense hsym h0
  exact sub_eq_zero.1 this

/-! ## Part 3 — the absolute value `|Ā| = (A* Ā)^{1/2}` -/

/-- `R^{1/2}` for the resolvent `R = (1 + A* Ā)⁻¹`. -/
noncomputable def absB (A : D →ₗ[ℂ] F) : F →L[ℂ] F := sqrtOp (resCLM A)

/-- `(1 − R)^{1/2}` for the resolvent `R = (1 + A* Ā)⁻¹`. -/
noncomputable def absC (A : D →ₗ[ℂ] F) : F →L[ℂ] F := coSqrtOp (resCLM A)

/-- **The absolute value `|Ā|`**, as a linear relation: the set of pairs
`(R^{1/2} y, (1 − R)^{1/2} y)`.  Formally `|Ā| = (1 − R)^{1/2} R^{-1/2}`, the
positive square root of `A* Ā = R⁻¹ − 1`. -/
noncomputable def absRel (A : D →ₗ[ℂ] F) : Submodule ℂ (F × F) :=
  LinearMap.range ((absB A).toLinearMap.prod (absC A).toLinearMap)

theorem mem_absRel_iff {A : D →ₗ[ℂ] F} {p : F × F} :
    p ∈ absRel A ↔ ∃ y, absB A y = p.1 ∧ absC A y = p.2 := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simp [← hy], by simp [← hy]⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨y, Prod.ext h1 h2⟩

theorem mem_absRel (A : D →ₗ[ℂ] F) (y : F) : (absB A y, absC A y) ∈ absRel A :=
  mem_absRel_iff.2 ⟨y, rfl, rfl⟩

theorem absB_mul_absB (A : D →ₗ[ℂ] F) : absB A * absB A = resCLM A :=
  sqrtOp_mul_self (resCLM_nonneg A) (resCLM_le_one A)

theorem absC_mul_absC (A : D →ₗ[ℂ] F) : absC A * absC A = 1 - resCLM A :=
  coSqrtOp_mul_self (resCLM_nonneg A) (resCLM_le_one A)

theorem absB_mul_absC (A : D →ₗ[ℂ] F) : absB A * absC A = midOp (resCLM A) :=
  sqrtOp_mul_coSqrtOp (resCLM_nonneg A)

theorem absC_mul_absB (A : D →ₗ[ℂ] F) : absC A * absB A = midOp (resCLM A) :=
  coSqrtOp_mul_sqrtOp (resCLM_nonneg A)

theorem isSelfAdjoint_absB (A : D →ₗ[ℂ] F) : IsSelfAdjoint (absB A) :=
  isSelfAdjoint_sqrtOp _

theorem isSelfAdjoint_absC (A : D →ₗ[ℂ] F) : IsSelfAdjoint (absC A) :=
  isSelfAdjoint_coSqrtOp _

theorem absB_absB_apply (A : D →ₗ[ℂ] F) (y : F) : absB A (absB A y) = resCLM A y := by
  have h : (absB A * absB A) y = resCLM A y := by rw [absB_mul_absB]
  exact h

theorem absC_absC_apply (A : D →ₗ[ℂ] F) (y : F) : absC A (absC A y) = y - resCLM A y := by
  have h : (absC A * absC A) y = ((1 : F →L[ℂ] F) - resCLM A) y := by rw [absC_mul_absC]
  simpa using h

theorem absB_absC_apply (A : D →ₗ[ℂ] F) (y : F) : absB A (absC A y) = absC A (absB A y) := by
  have h1 : (absB A * absC A) y = midOp (resCLM A) y := by rw [absB_mul_absC]
  have h2 : (absC A * absB A) y = midOp (resCLM A) y := by rw [absC_mul_absB]
  exact h1.trans h2.symm

theorem absB_injective (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    Function.Injective (absB A) :=
  sqrtOp_injective (resCLM_nonneg A) (resCLM_le_one A) (resCLM_injective A hdense hsym)

/-- **`|Ā|` is symmetric.** -/
theorem absRel_le_adjPairs (A : D →ₗ[ℂ] F) : absRel A ≤ adjPairs (absRel A) := by
  intro p hp q hq
  obtain ⟨y, hy1, hy2⟩ := mem_absRel_iff.1 hp
  obtain ⟨z, hz1, hz2⟩ := mem_absRel_iff.1 hq
  rw [← hy1, ← hy2, ← hz1, ← hz2,
    inner_isSelfAdjoint_left (isSelfAdjoint_absC A),
    inner_isSelfAdjoint_left (isSelfAdjoint_absB A), absB_absC_apply]

/-- **`1 + |Ā|` is surjective.** -/
theorem exists_mem_absRel_add (A : D →ₗ[ℂ] F) (h : F) :
    ∃ p ∈ absRel A, p.1 + p.2 = h := by
  obtain ⟨y, hy⟩ := exists_sqrtOp_add_coSqrtOp_eq (resCLM_nonneg A) (resCLM_le_one A) h
  exact ⟨(absB A y, absC A y), mem_absRel A y, hy⟩

/-- **`|Ā|` is self-adjoint.** -/
theorem adjPairs_absRel (A : D →ₗ[ℂ] F) : adjPairs (absRel A) = absRel A :=
  adjPairs_eq_self_of_symmetric_of_surjective (absRel_le_adjPairs A) (exists_mem_absRel_add A)

/-- The graph of `|Ā|` is closed. -/
theorem absRel_isClosed (A : D →ₗ[ℂ] F) :
    IsClosed ((absRel A : Submodule ℂ (F × F)) : Set (F × F)) := by
  rw [← adjPairs_absRel A]
  exact adjPairs_isClosed _

/-- **`|Ā|` is single-valued**: it is an operator, not merely a relation. -/
theorem absRel_snd_eq_zero_of_fst_eq_zero (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) {w : F} (h : ((0 : F), w) ∈ absRel A) : w = 0 := by
  obtain ⟨y, hy1, hy2⟩ := mem_absRel_iff.1 h
  simp only at hy1 hy2
  have hy0 : y = 0 := absB_injective A hdense hsym (by simpa using hy1)
  rw [← hy2, hy0, map_zero]

/-- **`|Ā| ≥ 0`**: its quadratic form is non-negative. -/
theorem absRel_quadForm_nonneg (A : D →ₗ[ℂ] F) {p : F × F} (hp : p ∈ absRel A) :
    0 ≤ (inner ℂ p.2 p.1 : ℂ) := by
  obtain ⟨y, hy1, hy2⟩ := mem_absRel_iff.1 hp
  have hpos : (midOp (resCLM A)).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 (midOp_nonneg _)
  have hmid : absC A (absB A y) = midOp (resCLM A) y := by
    have h : (absC A * absB A) y = midOp (resCLM A) y := by rw [absC_mul_absB]
    exact h
  rw [← hy1, ← hy2, inner_isSelfAdjoint_left (isSelfAdjoint_absC A), hmid]
  exact hpos.inner_nonneg_right y

/-- **`|Ā|² = A* Ā`.** -/
theorem absRel_comp_self (A : D →ₗ[ℂ] F) :
    {p : F × F | ∃ w, (p.1, w) ∈ absRel A ∧ (w, p.2) ∈ absRel A}
      = (factorRel A : Set (F × F)) := by
  ext p
  obtain ⟨x, z⟩ := p
  constructor
  · rintro ⟨w, hw1, hw2⟩
    obtain ⟨y, hy1, hy2⟩ := mem_absRel_iff.1 hw1
    obtain ⟨y', hy1', hy2'⟩ := mem_absRel_iff.1 hw2
    simp only at hy1 hy2 hy1' hy2'
    -- `y = B (B y) + C (C y) = B (B y) + B z`, so `x = R h` for `h = B y + z`
    have hCC : absC A (absC A y) = absB A z := by
      rw [hy2, ← hy1', ← absB_absC_apply, hy2']
    have hy : y = absB A (absB A y + z) := by
      have h1 : absB A (absB A y) + absC A (absC A y) = y := by
        rw [absB_absB_apply, absC_absC_apply]; abel
      rw [map_add, ← hCC, h1]
    have hx : x = resCLM A (absB A y + z) := by
      rw [← hy1]
      conv_lhs => rw [hy]
      rw [absB_absB_apply]
    have hsum : x + z = absB A y + z := by rw [← hy1]
    have hmem := resLin_mem_factorRel A (absB A y + z)
    have hx' : resLin A (absB A y + z) = x := hx.symm
    rw [hx'] at hmem
    have h2 : absB A y + z - x = z := by rw [← hsum]; abel
    rw [h2] at hmem
    exact hmem
  · intro hp
    have hres : resLin A (x + z) = x := by
      have h := resPair_unique (h := x + z) hp rfl
      rw [resLin_apply, h]
    have hRx : resCLM A (x + z) = x := hres
    refine ⟨absC A (absB A (x + z)), ?_, ?_⟩
    · refine mem_absRel_iff.2 ⟨absB A (x + z), ?_, rfl⟩
      rw [absB_absB_apply, hRx]
    · refine mem_absRel_iff.2 ⟨absC A (x + z), ?_, ?_⟩
      · exact (absB_absC_apply A (x + z)).symm ▸ rfl
      · have h1 : absC A (absC A (x + z)) = (x + z) - resCLM A (x + z) := absC_absC_apply A (x + z)
        rw [h1, hRx]
        abel

/-! ## Part 4 — `|Ā|` as an operator, and `D(|Ā|) = D(Ā)` with `‖ |Ā| x ‖ = ‖Āx‖` -/

/-- The domain of `|Ā|`: the range of `R^{1/2}`. -/
noncomputable def absDom (A : D →ₗ[ℂ] F) : Submodule ℂ F :=
  (absRel A).map (LinearMap.fst ℂ F F)

theorem mem_absDom_iff {A : D →ₗ[ℂ] F} {x : F} : x ∈ absDom A ↔ ∃ w, (x, w) ∈ absRel A := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨w, hw⟩
    exact ⟨(x, w), hw, rfl⟩

theorem mem_absDom_iff_range {A : D →ₗ[ℂ] F} {x : F} : x ∈ absDom A ↔ ∃ y, absB A y = x := by
  rw [mem_absDom_iff]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨y, hy1, -⟩ := mem_absRel_iff.1 hw
    exact ⟨y, hy1⟩
  · rintro ⟨y, rfl⟩
    exact ⟨absC A y, mem_absRel A y⟩

/-- The value of `|Ā|` at a point of its domain (chosen; unique by `absFun_unique`). -/
noncomputable def absFun (A : D →ₗ[ℂ] F) (x : absDom A) : F :=
  Classical.choose (mem_absDom_iff.1 x.2)

theorem absFun_spec (A : D →ₗ[ℂ] F) (x : absDom A) : ((x : F), absFun A x) ∈ absRel A :=
  Classical.choose_spec (mem_absDom_iff.1 x.2)

theorem absFun_unique {A : D →ₗ[ℂ] F} (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A)
    {x : absDom A} {w : F} (h : ((x : F), w) ∈ absRel A) : absFun A x = w := by
  have hz : ((0 : F), absFun A x - w) ∈ absRel A := by
    have := Submodule.sub_mem (absRel A) (absFun_spec A x) h
    simpa using this
  exact sub_eq_zero.mp (absRel_snd_eq_zero_of_fst_eq_zero A hdense hsym hz)

/-- **`|Ā|` as a linear operator** on its domain. -/
noncomputable def absOp (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    absDom A →ₗ[ℂ] F where
  toFun := absFun A
  map_add' x y := by
    refine absFun_unique hdense hsym ?_
    have := Submodule.add_mem (absRel A) (absFun_spec A x) (absFun_spec A y)
    simpa using this
  map_smul' c x := by
    refine absFun_unique hdense hsym ?_
    have := Submodule.smul_mem (absRel A) c (absFun_spec A x)
    simpa using this

@[simp] theorem absOp_apply (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) (x : absDom A) : absOp A hdense hsym x = absFun A x := rfl

theorem opGraph_absOp (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    opGraph (absOp A hdense hsym) = absRel A := by
  apply le_antisymm
  · rintro p ⟨x, rfl⟩
    simpa using absFun_spec A x
  · intro p hp
    have hx : p.1 ∈ absDom A := mem_absDom_iff.2 ⟨p.2, by simpa using hp⟩
    refine ⟨⟨p.1, hx⟩, ?_⟩
    have hval : absFun A ⟨p.1, hx⟩ = p.2 := absFun_unique hdense hsym (by simpa using hp)
    simp [hval]

/-- `|Ā|` is a closed operator: its graph is already closed. -/
theorem clGraph_absOp (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    clGraph (absOp A hdense hsym) = absRel A := by
  unfold clGraph
  rw [opGraph_absOp A hdense hsym]
  exact (absRel_isClosed A).submodule_topologicalClosure_eq

/-- **The domain of `|Ā|` is dense**: `R^{1/2}` is self-adjoint and injective. -/
theorem absDom_dense (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    Dense ((absDom A : Submodule ℂ F) : Set F) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  have hBv : absB A v = 0 := by
    have hzero : ∀ u : F, (inner ℂ u (absB A v) : ℂ) = 0 := by
      intro u
      have hmem : absB A u ∈ absDom A := mem_absDom_iff_range.2 ⟨u, rfl⟩
      have h0 := hv _ hmem
      rwa [inner_isSelfAdjoint_left (isSelfAdjoint_absB A)] at h0
    exact inner_self_eq_zero.1 (hzero (absB A v))
  exact absB_injective A hdense hsym (by simpa using hBv)

/-- `|Ā|` is symmetric on its domain. -/
theorem symmetricOn_absOp (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) : SymmetricOn (absDom A) (absOp A hdense hsym) := by
  intro x y
  have hx := absFun_spec A x
  have hy := absFun_spec A y
  have := absRel_le_adjPairs A hy ((x : F), absFun A x) hx
  simpa using this

theorem adjGraph_absOp (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    adjGraph (absOp A hdense hsym) = absRel A := by
  unfold adjGraph
  rw [opGraph_absOp A hdense hsym, adjPairs_absRel A]

/-- **The composite `|Ā|* ‾|Ā| = |Ā|²` is `A* Ā`.** -/
theorem factorRel_absOp (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    factorRel (absOp A hdense hsym) = factorRel A := by
  refine SetLike.ext' ?_
  rw [coe_factorRel, coe_factorRel]
  have h : factorGraph (absOp A hdense hsym)
      = {p : F × F | ∃ w, (p.1, w) ∈ absRel A ∧ (w, p.2) ∈ absRel A} := by
    ext p
    unfold factorGraph
    rw [clGraph_absOp A hdense hsym, adjGraph_absOp A hdense hsym]
  rw [h, absRel_comp_self A]
  rfl

theorem frDom_absOp (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    frDom (absOp A hdense hsym) = frDom A := by
  unfold frDom
  rw [factorRel_absOp A hdense hsym]

/-- **von Neumann's core theorem for `|Ā|`**: `D(A* Ā)` is a core of `|Ā|` too. -/
theorem topologicalClosure_coreGraph_absOp (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) :
    (absRel A ⊓ (frDom A).comap (LinearMap.fst ℂ F F)).topologicalClosure = absRel A := by
  have h := topologicalClosure_coreGraph (absOp A hdense hsym) (absDom_dense A hdense hsym)
    (symmetricOn_absOp A hdense hsym)
  unfold coreGraph at h
  rw [clGraph_absOp A hdense hsym, frDom_absOp A hdense hsym] at h
  exact h

/-- The two closed relations agree in norm over the common core `D(A* Ā)`. -/
theorem norm_eq_of_mem_frDom (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) {x w y : F} (hx : x ∈ frDom A) (hxw : (x, w) ∈ absRel A)
    (hxy : (x, y) ∈ clGraph A) : ‖w‖ = ‖y‖ := by
  obtain ⟨z, hz⟩ := mem_frDom_iff.1 hx
  -- the quadratic form of `A* Ā` at `x` is `‖Āx‖²`
  obtain ⟨y', hy', hquad⟩ := factorGraph_quadForm (A := A) (p := (x, z)) hz
  have hyy : y' = y := by
    have h0 : ((0 : F), y' - y) ∈ clGraph A := by
      have := Submodule.sub_mem (clGraph A) hy' hxy
      simpa using this
    exact sub_eq_zero.1 (clGraph_snd_eq_zero_of_fst_eq_zero hdense hsym h0)
  -- and it is `‖ |Ā| x ‖²`
  have hcomp : ((x, z) : F × F) ∈ {p : F × F | ∃ v, (p.1, v) ∈ absRel A ∧ (v, p.2) ∈ absRel A} := by
    rw [absRel_comp_self A]
    exact hz
  obtain ⟨w', hw'1, hw'2⟩ := hcomp
  simp only at hw'1 hw'2
  have hww : w' = w := by
    have h0 : ((0 : F), w' - w) ∈ absRel A := by
      have := Submodule.sub_mem (absRel A) hw'1 hxw
      simpa using this
    exact sub_eq_zero.1 (absRel_snd_eq_zero_of_fst_eq_zero A hdense hsym h0)
  have hnormw : (inner ℂ w w : ℂ) = inner ℂ x z := by
    have := absRel_le_adjPairs A (hww ▸ hw'2) (x, w) hxw
    simpa using this
  have hfin : ((‖w‖ ^ 2 : ℝ) : ℂ) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : (inner ℂ w w : ℂ) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [← h1, hnormw]
    simpa [hyy] using hquad
  have hsq : ‖w‖ ^ 2 = ‖y‖ ^ 2 := by exact_mod_cast hfin
  nlinarith [norm_nonneg w, norm_nonneg y]

/-- **Transfer along a core.**  If a closed single-valued relation `G` matches a
subspace `K` of pairs in norm, it matches the whole closure of `K`. -/
theorem exists_of_mem_topologicalClosure {K G : Submodule ℂ (F × F)}
    (hGclosed : IsClosed ((G : Submodule ℂ (F × F)) : Set (F × F)))
    (hGsv : ∀ w : F, ((0 : F), w) ∈ G → w = 0)
    (hK : ∀ p ∈ K, ∃ w, (p.1, w) ∈ G ∧ ‖w‖ = ‖p.2‖)
    {p : F × F} (hp : p ∈ K.topologicalClosure) :
    ∃ w, (p.1, w) ∈ G ∧ ‖w‖ = ‖p.2‖ := by
  have hmem : p ∈ closure ((K : Submodule ℂ (F × F)) : Set (F × F)) := by
    rwa [← Submodule.topologicalClosure_coe]
  obtain ⟨q, hqK, hq⟩ := mem_closure_iff_seq_limit.1 hmem
  choose w hw hnorm using fun n => hK (q n) (hqK n)
  have hdiff : ∀ n m, ‖w n - w m‖ = ‖(q n).2 - (q m).2‖ := by
    intro n m
    obtain ⟨u, hu, hnu⟩ := hK _ (K.sub_mem (hqK n) (hqK m))
    have hg : ((q n - q m).1, w n - w m) ∈ G := by
      have := G.sub_mem (hw n) (hw m)
      simpa using this
    have hueq : u = w n - w m := by
      have h0 : ((0 : F), u - (w n - w m)) ∈ G := by
        have := G.sub_mem hu hg
        simpa using this
      exact sub_eq_zero.1 (hGsv _ h0)
    rw [← hueq, hnu]
    simp
  have hq2 : Filter.Tendsto (fun n => (q n).2) Filter.atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hq
  have hq1 : Filter.Tendsto (fun n => (q n).1) Filter.atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hq
  have hcw : CauchySeq w := by
    rw [Metric.cauchySeq_iff]
    have hc2 : CauchySeq (fun n => (q n).2) := hq2.cauchySeq
    rw [Metric.cauchySeq_iff] at hc2
    intro ε hε
    obtain ⟨N, hN⟩ := hc2 ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    have := hN n hn m hm
    rwa [dist_eq_norm, ← hdiff n m, ← dist_eq_norm] at this
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcw
  refine ⟨v, ?_, ?_⟩
  · have hlim : Filter.Tendsto (fun n => ((q n).1, w n)) Filter.atTop (nhds (p.1, v)) :=
      hq1.prodMk_nhds hv
    exact hGclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => hw n)
  · have h1 : Filter.Tendsto (fun n => ‖w n‖) Filter.atTop (nhds ‖v‖) := hv.norm
    have h2 : Filter.Tendsto (fun n => ‖w n‖) Filter.atTop (nhds ‖p.2‖) := by
      simpa only [hnorm] using hq2.norm
    exact tendsto_nhds_unique h1 h2

/-- **Every vector of `D(Ā)` lies in `D(|Ā|)`, with the same norm.** -/
theorem exists_mem_absRel_of_mem_clGraph (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) {p : F × F} (hp : p ∈ clGraph A) :
    ∃ w, (p.1, w) ∈ absRel A ∧ ‖w‖ = ‖p.2‖ := by
  refine exists_of_mem_topologicalClosure (K := coreGraph A) (G := absRel A)
    (absRel_isClosed A) (fun w hw => absRel_snd_eq_zero_of_fst_eq_zero A hdense hsym hw)
    (fun r hr => ?_) ?_
  · obtain ⟨hrc, hrd⟩ := mem_coreGraph_iff.1 hr
    obtain ⟨z, hz⟩ := mem_frDom_iff.1 hrd
    have hcomp : ((r.1, z) : F × F)
        ∈ {s : F × F | ∃ v, (s.1, v) ∈ absRel A ∧ (v, s.2) ∈ absRel A} := by
      rw [absRel_comp_self A]; exact hz
    obtain ⟨v, hv1, -⟩ := hcomp
    simp only at hv1
    have hrc' : (r.1, r.2) ∈ clGraph A := by simpa using hrc
    exact ⟨v, hv1, norm_eq_of_mem_frDom A hdense hsym hrd hv1 hrc'⟩
  · rw [topologicalClosure_coreGraph A hdense hsym]
    exact hp

/-- **Every vector of `D(|Ā|)` lies in `D(Ā)`, with the same norm.** -/
theorem exists_mem_clGraph_of_mem_absRel (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) {p : F × F} (hp : p ∈ absRel A) :
    ∃ y, (p.1, y) ∈ clGraph A ∧ ‖y‖ = ‖p.2‖ := by
  refine exists_of_mem_topologicalClosure
    (K := absRel A ⊓ (frDom A).comap (LinearMap.fst ℂ F F)) (G := clGraph A)
    (clGraph_isClosed A) (fun y hy => clGraph_snd_eq_zero_of_fst_eq_zero hdense hsym hy)
    (fun r hr => ?_) ?_
  · obtain ⟨hra, hrd⟩ := hr
    have hrd' : r.1 ∈ frDom A := hrd
    have hmem : r.1 ∈ clDom A := frDom_le_clDom A hrd'
    obtain ⟨y, hy⟩ := mem_clDom_iff.1 hmem
    exact ⟨y, hy, (norm_eq_of_mem_frDom A hdense hsym hrd' hra hy).symm⟩
  · rw [topologicalClosure_coreGraph_absOp A hdense hsym]
    exact hp

/-- **`D(|Ā|) = D(Ā)`.** -/
theorem absDom_eq_clDom (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    absDom A = clDom A := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨w, hw⟩ := mem_absDom_iff.1 hx
    obtain ⟨y, hy, -⟩ := exists_mem_clGraph_of_mem_absRel A hdense hsym hw
    exact mem_clDom_iff.2 ⟨y, hy⟩
  · obtain ⟨y, hy⟩ := mem_clDom_iff.1 hx
    obtain ⟨w, hw, -⟩ := exists_mem_absRel_of_mem_clGraph A hdense hsym hy
    exact mem_absDom_iff.2 ⟨w, hw⟩

/-- **`‖ |Ā| x ‖ = ‖Ā x‖` for every `x` in the common domain.** -/
theorem norm_absFun_eq_norm_clFun (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) {x w y : F} (hxw : (x, w) ∈ absRel A) (hxy : (x, y) ∈ clGraph A) :
    ‖w‖ = ‖y‖ := by
  obtain ⟨y', hy', hn⟩ := exists_mem_clGraph_of_mem_absRel A hdense hsym hxw
  have hyy : y' = y := by
    have h0 : ((0 : F), y' - y) ∈ clGraph A := by
      have := Submodule.sub_mem (clGraph A) hy' hxy
      simpa using this
    exact sub_eq_zero.1 (clGraph_snd_eq_zero_of_fst_eq_zero hdense hsym h0)
  rw [← hyy]
  exact hn.symm

/-! ## Part 5 — the polar decomposition `Ā = U |Ā|` -/

omit [CompleteSpace F] in
/-- Polarization: two linear maps with the same norms have the same sesquilinear form. -/
theorem inner_eq_of_norm_eq {Dom : Submodule ℂ F} (P Q : Dom →ₗ[ℂ] F)
    (h : ∀ z : Dom, ‖P z‖ = ‖Q z‖) (x y : Dom) :
    (inner ℂ (P x) (P y) : ℂ) = inner ℂ (Q x) (Q y) := by
  have key : ∀ c : ℂ, ‖P x + c • P y‖ = ‖Q x + c • Q y‖ := by
    intro c
    have hP : P x + c • P y = P (x + c • y) := by rw [map_add, map_smul]
    have hQ : Q x + c • Q y = Q (x + c • y) := by rw [map_add, map_smul]
    rw [hP, hQ, h]
  have e1 : ‖P x + P y‖ = ‖Q x + Q y‖ := by simpa using key 1
  have e2 : ‖P x - P y‖ = ‖Q x - Q y‖ := by
    have := key (-1); simpa [sub_eq_add_neg] using this
  have e3 : ‖P x - (RCLike.I : ℂ) • P y‖ = ‖Q x - (RCLike.I : ℂ) • Q y‖ := by
    have := key (-(RCLike.I : ℂ)); simpa [sub_eq_add_neg] using this
  have e4 : ‖P x + (RCLike.I : ℂ) • P y‖ = ‖Q x + (RCLike.I : ℂ) • Q y‖ := key _
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4]

/-- `|Ā|` as an operator on the domain `D(Ā)` of the closure — the same domain,
by `absDom_eq_clDom`. -/
noncomputable def absOn (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    clDom A →ₗ[ℂ] F :=
  (absOp A hdense hsym).comp (Submodule.inclusion (absDom_eq_clDom A hdense hsym).ge)

theorem absOn_spec (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A)
    (x : clDom A) : ((x : F), absOn A hdense hsym x) ∈ absRel A :=
  absFun_spec A ⟨(x : F), (absDom_eq_clDom A hdense hsym).ge x.2⟩

/-- **`‖ |Ā| x ‖ = ‖Ā x ‖`.** -/
theorem norm_absOn (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A)
    (x : clDom A) : ‖absOn A hdense hsym x‖ = ‖clExt A hdense hsym x‖ :=
  norm_absFun_eq_norm_clFun A hdense hsym (absOn_spec A hdense hsym x) (clFun_spec A x)

/-- `⟪|Ā|x, |Ā|y⟫ = ⟪Āx, Āy⟫`: the two operators have the same form. -/
theorem inner_absOn (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A)
    (x y : clDom A) :
    (inner ℂ (absOn A hdense hsym x) (absOn A hdense hsym y) : ℂ)
      = inner ℂ (clExt A hdense hsym x) (clExt A hdense hsym y) :=
  inner_eq_of_norm_eq _ _ (norm_absOn A hdense hsym) x y

/-- **The polar decomposition `Ā = U |Ā|`.**  There is a linear isometry `U`
from `ran |Ā|` into `F`, with range `ran Ā`, such that `U (|Ā| x) = Ā x` for
every `x` in the common domain `D(|Ā|) = D(Ā)`. -/
theorem exists_polar_isometry (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) :
    ∃ U : LinearMap.range (absOn A hdense hsym) →ₗ[ℂ] F,
      (∀ x : clDom A, U ⟨absOn A hdense hsym x,
        LinearMap.mem_range_self (absOn A hdense hsym) x⟩ = clExt A hdense hsym x) ∧
      (∀ z : LinearMap.range (absOn A hdense hsym), ‖U z‖ = ‖(z : F)‖) ∧
      LinearMap.range U = LinearMap.range (clExt A hdense hsym) :=
  exists_linearIsometry_of_inner_eq (absOn A hdense hsym) (clExt A hdense hsym)
    (inner_absOn A hdense hsym)

end Resolvent

end BookProof.UnboundedPolar


