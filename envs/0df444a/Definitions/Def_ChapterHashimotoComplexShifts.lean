-- Prove2me | Definitions.Def_ChapterHashimotoComplexShifts
-- name    : ChapterHashimotoComplexShifts
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:03:12.975385+00:00
-- url     : https://prove2.me/theorems/33c42b76-32d9-4d5e-83c9-d70fcb3392f3
-- title:
--   `BookProof.ChapterHashimotoShiftInvert` develops the shift-invert trick for a *single, real, positive* shift `γ`, where ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HashimotoComplexShifts`, source chapter `BookProof/ChapterHashimotoComplexShifts.lean`).
--
--   `BookProof.ChapterHashimotoShiftInvert` develops the shift-invert trick for a *single, real, positive* shift `γ`, where invertibility of `A + γ` comes from positivity of `A`. The Shift-invert Rational Krylov method of Hashimoto and Nodera is however run with
--
--   * shifts `γ` that are **complex with non-zero imaginary part** — then `γ I − A` is invertible for *every* self-adjoint `A`, with no positivity assumption at all, purely because a non-real number is at distance `|Im γ| > 0` from the (real) numerical range; and * **many different shifts** `γ₁, γ₂, …`, one per step, the rational Krylov subspace `Q_m({X_j}, v) = span{v, X₁v, X₂X₁v, …, X_{m-1}⋯X₁v}` being built out of the resolvents `X_j = (γ_j I − A)⁻¹`.
--
--   This module adapts the theory to that setting. Everything is in the same namespace `BookProof.HashimotoShiftInvert`.
--
--   `norm_cshiftMap_ge`: `‖(γ − A)x‖ ≥ |Im γ| ‖x‖` for a **symmetric** `A`, with no positivity. Hence `cshiftMap_injective`.
--
--   `cshiftRange_isClosed`, `cshiftRange_orthogonal_eq_bot`, `cshiftMap_surjective`: for a self-adjoint `A` (symmetry plus the adjoint criterion) and non-real `γ`, `γ − A` is a bijection of `Dom` onto the whole space.
--
--   `IsShiftInvertC`, `exists_isShiftInvertC`, `IsShiftInvertC.opNorm_le` (`‖X‖ ≤ 1/|Im γ|`), `IsShiftInvertC.adjoint_eq` (the adjoint of `X` is the resolvent at the conjugate shift — `X` is no longer self-adjoint, it is normal), `shiftInvertC_determines`, `isShiftInvertC_unique`, and `isShiftInvertC_neg_of_isShiftInvert` relating the new theory to the real positive-shift theory of the previous chapter.
--
--   `shiftInvertC_resolvent_identity` (`X_j − X_k = (γ_k − γ_j) X_j X_k`), `shiftInvertC_commute`, `shiftInvertC_comp_one_sub` (the SIRK relation `X_j (I − (γ_m − γ_j) X_m) = X_m`), the rational Krylov flag `rkVec`, `rkSpan`, and `rkSpan_den_eq` — the cleared-denominator form of Hashimoto–Nodera Eq. (11): `∏_{i<k} (I − (γ_m − γ_i)X_m)` maps the `k`-th rational Krylov vector to `X_m^k v`, so the rational Krylov subspace built from many shifts is a space of *rational* functions of the single resolvent `X_m`. `rkCompression_tendsto` gives strong convergence of the compressions along the flag.
--
--   `hashimoto_multishift_selects_friedrichs`.
--
--   The number operator `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, its resolvents at arbitrary non-real shifts, and `hashimoto_multishift_unbounded_example`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterComplexShiftCore

import Mathlib

/-!
# The Hashimoto (SIRK) algorithm with **complex, non-real, and many different shifts**

`BookProof.ChapterHashimotoShiftInvert` develops the shift-invert trick for a
*single, real, positive* shift `γ`, where invertibility of `A + γ` comes from
positivity of `A`.  The Shift-invert Rational Krylov method of Hashimoto and
Nodera is however run with

* shifts `γ` that are **complex with non-zero imaginary part** — then
  `γ I − A` is invertible for *every* self-adjoint `A`, with no positivity
  assumption at all, purely because a non-real number is at distance
  `|Im γ| > 0` from the (real) numerical range; and
* **many different shifts** `γ₁, γ₂, …`, one per step, the rational Krylov
  subspace `Q_m({X_j}, v) = span{v, X₁v, X₂X₁v, …, X_{m-1}⋯X₁v}` being built
  out of the resolvents `X_j = (γ_j I − A)⁻¹`.

This module adapts the theory to that setting.  Everything is in the same
namespace `BookProof.HashimotoShiftInvert`.

## Part 1 — the non-real shift bound

`norm_cshiftMap_ge`: `‖(γ − A)x‖ ≥ |Im γ| ‖x‖` for a **symmetric** `A`, with no
positivity.  Hence `cshiftMap_injective`.

## Part 2 — bijectivity

`cshiftRange_isClosed`, `cshiftRange_orthogonal_eq_bot`, `cshiftMap_surjective`:
for a self-adjoint `A` (symmetry plus the adjoint criterion) and non-real `γ`,
`γ − A` is a bijection of `Dom` onto the whole space.

## Part 3 — the resolvent `X = (γ − A)⁻¹`

`IsShiftInvertC`, `exists_isShiftInvertC`, `IsShiftInvertC.opNorm_le`
(`‖X‖ ≤ 1/|Im γ|`), `IsShiftInvertC.adjoint_eq` (the adjoint of `X` is the
resolvent at the conjugate shift — `X` is no longer self-adjoint, it is normal),
`shiftInvertC_determines`, `isShiftInvertC_unique`, and
`isShiftInvertC_neg_of_isShiftInvert` relating the new theory to the real
positive-shift theory of the previous chapter.

## Part 4 — many shifts

`shiftInvertC_resolvent_identity` (`X_j − X_k = (γ_k − γ_j) X_j X_k`),
`shiftInvertC_commute`, `shiftInvertC_comp_one_sub` (the SIRK relation
`X_j (I − (γ_m − γ_j) X_m) = X_m`), the rational Krylov flag `rkVec`,
`rkSpan`, and `rkSpan_den_eq` — the cleared-denominator form of Hashimoto–Nodera
Eq. (11): `∏_{i<k} (I − (γ_m − γ_i)X_m)` maps the `k`-th rational Krylov vector
to `X_m^k v`, so the rational Krylov subspace built from many shifts is a space
of *rational* functions of the single resolvent `X_m`.  `rkCompression_tendsto`
gives strong convergence of the compressions along the flag.

## Part 5 — the headline

`hashimoto_multishift_selects_friedrichs`.

## Part 6 — a genuinely unbounded example with non-real shifts

The number operator `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, its resolvents at arbitrary
non-real shifts, and `hashimoto_multishift_unbounded_example`.
-/

namespace BookProof.HashimotoShiftInvert

open Filter Topology


/-! ## Part 3 — the resolvent `X = (γ I − A)⁻¹` at a non-real shift -/

section CShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

/-- `X` is the **resolvent (shift-invert) of `A` at the complex shift `γ`**: a
bounded everywhere-defined operator inverting `γ I − A` in both directions. -/
def IsShiftInvertC (A : Dom →ₗ[ℂ] F) (γ : ℂ) (X : F →L[ℂ] F) : Prop :=
  (∀ x : Dom, X (cshiftMap A γ x) = (x : F)) ∧
    ∀ u : F, ∃ h : X u ∈ Dom, cshiftMap A γ ⟨X u, h⟩ = u



























end CShiftInvert

/-! ## Part 4 — many shifts: the rational Krylov structure -/

section ManyShifts

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}







/-- The `k`-th vector of the **rational Krylov sequence** with shifts `X 0, X 1, …`:
`v, X₀v, X₁X₀v, …` — the vectors spanning `Q_m({X_j}, v)` of Eq. (8). -/
noncomputable def rkVec (X : ℕ → F →L[ℂ] F) (v : F) : ℕ → F
  | 0 => v
  | k + 1 => X k (rkVec X v k)





/-- The **rational Krylov subspace** `Q_m({X_j}, v)` of Eq. (8). -/
noncomputable def rkSpan (X : ℕ → F →L[ℂ] F) (v : F) (m : ℕ) : Submodule ℂ F :=
  Submodule.span ℂ (rkVec X v '' {k | k < m})



instance rkSpan_finiteDimensional (X : ℕ → F →L[ℂ] F) (v : F) (m : ℕ) :
    FiniteDimensional ℂ (rkSpan X v m) :=
  FiniteDimensional.span_of_finite ℂ ((Set.finite_Iio m).image _)

/-- The **denominator** `∏_{i<k} (I − (γ_m − γ_i) X_m)` of the rational function
of Eq. (11), built up recursively. -/
noncomputable def sirkDen (Xm : F →L[ℂ] F) (c : ℕ → ℂ) : ℕ → F →L[ℂ] F
  | 0 => ContinuousLinearMap.id ℂ F
  | k + 1 => (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L sirkDen Xm c k









end ManyShifts

/-! ## Part 4b — convergence of the compressions along the rational Krylov flag -/

section RkConvergence

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The **rational Krylov (Hashimoto/SIRK) compression** `P_m T P_m` of a bounded
operator along the flag of rational Krylov subspaces generated by the shifts. -/
noncomputable def rkCompression (T : F →L[ℂ] F) (X : ℕ → F →L[ℂ] F) (v : F) (m : ℕ) :
    F →L[ℂ] F :=
  (rkSpan X v m).starProjection ∘L T ∘L (rkSpan X v m).starProjection





end RkConvergence

/-! ## Part 5 — the headline theorem for complex, multiple shifts -/

section Headline

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



end Headline

/-! ## Part 6 — a genuinely unbounded example with non-real shifts

The number operator `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)` of
`BookProof.ChapterHashimotoShiftInvert`, whose resolvent at a shift `γ` off the
real axis is the bounded complex diagonal operator `eₙ ↦ eₙ/(γ − n)`.  Running
the algorithm with a whole sequence of such shifts is therefore not vacuous. -/

section UnboundedExample

open scoped InnerProductSpace ENNReal lp

/-! ### Complex diagonal operators on `ℓ²(ℕ, ℂ)` -/

theorem memlp_diagFunC {c : ℕ → ℂ} {M : ℝ} (hc : ∀ n, ‖c n‖ ≤ M) (x : ℓ²(ℕ, ℂ)) :
    Memℓp (fun n => c n * x n) 2 := by
  have hx : Summable fun n => ‖(x : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp x).summable (by norm_num)
  refine memℓp_gen (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hx.mul_left (M ^ 2)))
  have ht : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [ht, Real.rpow_two, Real.rpow_two, norm_mul, mul_pow]
  gcongr
  exact hc n

/-- The diagonal (multiplication) operator on `ℓ²(ℕ, ℂ)` with **complex**
coefficients bounded by `M`, as a linear map. -/
noncomputable def diagLinC {c : ℕ → ℂ} {M : ℝ} (hc : ∀ n, ‖c n‖ ≤ M) :
    ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun x := ⟨fun n => c n * x n, memlp_diagFunC hc x⟩
  map_add' x y := by
    apply lp.ext; funext n
    simp only [lp.coeFn_add]
    dsimp [PreLp]
    rw [mul_add]
  map_smul' a x := by
    apply lp.ext; funext n
    simp only [lp.coeFn_smul]
    dsimp [PreLp]
    ring



theorem diagLinC_norm_le {c : ℕ → ℂ} {M : ℝ} (hc : ∀ n, ‖c n‖ ≤ M) (x : ℓ²(ℕ, ℂ)) :
    ‖diagLinC hc x‖ ≤ M * ‖x‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg (c 0)) (hc 0)
  refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
  have hMx : Summable fun n => M ^ (2 : ℝ≥0∞).toReal * ‖(x : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
    ((lp.memℓp x).summable (by norm_num)).mul_left _
  refine le_trans (Summable.tsum_le_tsum (fun n => ?_)
    ((memlp_diagFunC hc x).summable (by norm_num)) hMx) ?_
  · have ht : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    change ‖c n * (x : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal ≤ _
    rw [ht, Real.rpow_two, Real.rpow_two, Real.rpow_two, norm_mul, mul_pow]
    gcongr
    exact hc n
  · rw [tsum_mul_left, ← lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact le_of_eq (Real.mul_rpow hM (norm_nonneg x)).symm

/-- The complex diagonal operator as a bounded operator, of norm at most `M`. -/
noncomputable def diagCLMC {c : ℕ → ℂ} {M : ℝ} (hc : ∀ n, ‖c n‖ ≤ M) :
    ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  (diagLinC hc).mkContinuous M (diagLinC_norm_le hc)



/-! ### The resolvents of the number operator at non-real shifts -/

/-- The coefficients `1/(γ − n)` of the resolvent of the number operator. -/
noncomputable def resCoeff (γ : ℂ) (n : ℕ) : ℂ := 1 / (γ - n)

/-- The coefficients `(n+1)/(γ − n)`: applying `R = (A+1)⁻¹` to this diagonal
gives the resolvent, which is how one sees that the resolvent lands in the
domain of `A`. -/
noncomputable def preCoeff (γ : ℂ) (n : ℕ) : ℂ := ((n : ℂ) + 1) / (γ - n)

theorem norm_sub_natCast_ge (γ : ℂ) (n : ℕ) : |γ.im| ≤ ‖γ - (n : ℂ)‖ := by
  have h := Complex.abs_im_le_norm (γ - (n : ℂ))
  simpa using h



theorem resCoeff_norm_le {γ : ℂ} (hγ : γ.im ≠ 0) (n : ℕ) : ‖resCoeff γ n‖ ≤ |γ.im|⁻¹ := by
  have hd : 0 < |γ.im| := abs_pos.mpr hγ
  have hw : |γ.im| ≤ ‖γ - (n : ℂ)‖ := norm_sub_natCast_ge γ n
  have hwpos : 0 < ‖γ - (n : ℂ)‖ := lt_of_lt_of_le hd hw
  rw [resCoeff, norm_div, norm_one, div_le_iff₀ hwpos, inv_mul_eq_div, le_div_iff₀ hd]
  nlinarith

theorem preCoeff_norm_le {γ : ℂ} (hγ : γ.im ≠ 0) (n : ℕ) :
    ‖preCoeff γ n‖ ≤ 1 + (|γ.re| + 1) / |γ.im| := by
  have hd : 0 < |γ.im| := abs_pos.mpr hγ
  have hw : |γ.im| ≤ ‖γ - (n : ℂ)‖ := norm_sub_natCast_ge γ n
  have hwpos : 0 < ‖γ - (n : ℂ)‖ := lt_of_lt_of_le hd hw
  have hre : |γ.re - (n : ℝ)| ≤ ‖γ - (n : ℂ)‖ := by
    have h := Complex.abs_re_le_norm (γ - (n : ℂ))
    simpa using h
  have hnum : ((n : ℝ) + 1) ≤ ‖γ - (n : ℂ)‖ + (|γ.re| + 1) := by
    have h1 : (n : ℝ) - γ.re ≤ |γ.re - (n : ℝ)| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have h2 : γ.re ≤ |γ.re| := le_abs_self _
    linarith
  have hnorm : ‖preCoeff γ n‖ = ((n : ℝ) + 1) / ‖γ - (n : ℂ)‖ := by
    rw [preCoeff, norm_div]
    congr 1
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) by push_cast; ring, Complex.norm_natCast]
    push_cast
    ring
  rw [hnorm, div_le_iff₀ hwpos]
  have hkey : (|γ.re| + 1) ≤ (|γ.re| + 1) / |γ.im| * ‖γ - (n : ℂ)‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    nlinarith [abs_nonneg γ.re]
  nlinarith

/-- **The resolvent of the number operator at a non-real shift**: the bounded
complex diagonal operator `eₙ ↦ eₙ/(γ − n)`, of norm at most `1/|Im γ|`. -/
noncomputable def ell2Resolvent {γ : ℂ} (hγ : γ.im ≠ 0) : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  diagCLMC (resCoeff_norm_le hγ)

/-- The auxiliary diagonal `eₙ ↦ (n+1) eₙ/(γ − n)`, a preimage of the resolvent
under `R = (A+1)⁻¹`. -/
noncomputable def ell2ResolventPre {γ : ℂ} (hγ : γ.im ≠ 0) : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  diagCLMC (preCoeff_norm_le hγ)









end UnboundedExample

end BookProof.HashimotoShiftInvert


