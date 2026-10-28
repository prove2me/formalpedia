-- Prove2me | Definitions.Def_ChapterResolventMinMaxLadder
-- name    : ChapterResolventMinMaxLadder
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T14:21:35.19801+00:00
-- url     : https://prove2.me/theorems/eb4ed8b9-6770-4f8a-88d5-6bae81393980
-- title:
--   Chapter ResolventMinMaxLadder
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterResolventMinMaxLadder.lean`): generated def bundle for ChapterResolventMinMaxLadder. See BookProof/ChapterResolventMinMaxLadder.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterResolventMinMaxLadder.lean

import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterSirkRitzMinMax
import Theorems.Thm_BookProof_RitzMinMax_neg_norm_le_rayleighVal_of_unit
import Theorems.Thm_BookProof_RitzMinMax_rayleighVal_le_norm_of_unit
import Theorems.Thm_BookProof_RitzMinMax_exists_unit_mem
import Theorems.Thm_BookProof_RitzMinMax_rayleighSetOn_nonempty
import Theorems.Thm_BookProof_RitzMinMax_rayleighSetOn_span_singleton
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_sInf_spectrum_eq_rayleighInf
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_rayleighSet_nonempty
import Theorems.Thm_BookProof_RitzMinMax_minmaxLevel_le_minmaxLevelIn
import Theorems.Thm_BookProof_RitzMinMax_galerkin_minmaxLevel_tendsto
import Mathlib


/-!
# Chapter ResolventMinMaxLadder — the Courant–Fischer ladder of an **unbounded**
# non-negative self-adjoint relation, through its resolvent

`CONSOLIDATED_PLAN.md` records, as the QG next step, "the min–max ladder through the
resolvent for the continuum spectral claim", and the recorded honest boundary of
`BookProof.ChapterSirkRitzMinMax` / `BookProof.ChapterMinMaxSpectrum` is that *the operator
is bounded throughout — the unbounded case is reached through the resolvent, not directly*.

This chapter takes that step.  Let `T` be a non-negative self-adjoint linear relation on a
complex Hilbert space `F` (the object produced by the project's Friedrichs / essential
self-adjointness chapters) and let

```text
R = (T + 1)⁻¹      (`BookProof.NonnegSquareRoot.invCLMAt`, here `res hT`)
```

be its resolvent at `1`: a **bounded**, self-adjoint, non-negative operator, to which the
whole bounded min–max machinery applies.  The ladder of `T` is compared with the ladder of
`R` read **from the top** (`maxminLevel`), through the decreasing bijection
`λ ↦ 1/(1 + λ)`.

## The analytic core

For `(y, z) ∈ T` put `x = y + z`, so that `R x = y`.  Cauchy–Schwarz for the non-negative
form `(u, v) ↦ Re⟪u, R v⟫` applied to the pair `(x, R x)` gives `‖R x‖⁴ ≤ ⟪x, Rx⟫ ⟪Rx, RRx⟫`,
which in terms of `T` is the **pointwise ladder inequality**

```text
‖y‖⁴ ≤ (‖y‖² + Re⟪y, z⟫) · Re⟪y, R y⟫,
```

i.e. for a unit vector of the domain, `Re⟪y, z⟫ ≥ 1/Re⟪y, R y⟫ − 1`.  It is the operator
form of Jensen's inequality for the convex function `λ ↦ 1/(1 + λ)`, proved with no spectral
theory at all.

## Deliverables

* `posForm_cauchy_schwarz`, `normSq_sq_le_rayleigh_mul` — Cauchy–Schwarz for a non-negative
  bounded form, and its consequence `‖Rx‖⁴ ≤ rayleighVal R x · rayleighVal R (R x)`.
* `res`, `res_mem`, `res_eq_of_mem`, `res_injective` — the resolvent at `1` as an operator
  onto the domain of `T`.
* **`normSq_sq_le_rayleigh_graph`**, `one_le_add_mul_rayleigh_of_unit`,
  `inv_sub_one_le_of_rayleigh_le` — the pointwise ladder inequality.
* `rayleighInfOn`, `maxminSet`, `maxminLevel` — the Courant–Fischer ladder of a bounded
  operator read from the top, with `maxminLevel_zero_eq_sSup_rayleighSet`.
* `graphRayleighSet`, `graphRayleighSup`, `InDomain`, `graphMinmaxSet`,
  `graphMinmaxLevel` — the ladder of the **relation** `T`, over the finite-dimensional
  subspaces of its domain; `graphRayleighSet_bddAbove` (a closed operator is bounded on a
  finite-dimensional subspace of its domain) and `graphMinmaxSet_nonempty` (the resolvent
  supplies subspaces of every dimension inside the domain).
* **`resolvent_ladder_lower`** — for every `k`,
  `1 / maxminLevel R k − 1 ≤ graphMinmaxLevel T k`: the ladder of the unbounded `T` is
  bounded below by the ladder of the bounded resolvent, read from the top.
* **`graphMinmaxLevel_zero_eq`** — at the bottom rung the inequality is an **equality**:
  `graphMinmaxLevel T 0 = 1 / maxminLevel R 0 − 1`, and
  `graphMinmaxLevel_zero_eq_sSup_spectrum` writes it with the top of the spectrum of `R`.
* `maxminLevelIn`, `minmaxLevel_neg`, `maxminLevelIn_le_maxminLevel`,
  **`galerkin_maxminLevel_tendsto`**, `galerkin_maxmin_gap_eventually_pos` and
  **`graphMinmaxLevel_zero_le_of_computed`** — the computational side: the ladder from the
  top is the ladder of `−R` from the bottom, so the Galerkin levels of the resolvent
  converge to it, a computed Ritz level is a lower bound for the true level, and therefore
  `1/(computed level) − 1` is a rigorous **upper** bound for the ground level of `T`.
* **`graphMinmax_gap_lower`** — hence a gap of the resolvent's ladder is a gap of `T`'s:
  `graphMinmaxLevel T 1 − graphMinmaxLevel T 0 ≥ 1 / maxminLevel R 1 − 1 / maxminLevel R 0`,
  and `graphMinmax_gap_pos`: it is **positive** as soon as `maxminLevel R 1 < maxminLevel R 0`.

## Honest boundary

In *this* chapter only the bottom rung of the ladder is an equality; for `k ≥ 1` what is
proved here is the inequality `1/ν_k − 1 ≤ μ_k`, which is the direction a **gap** statement
needs (a lower bound for the excited level together with the exact ground level).  The
reverse inequality for `k ≥ 1` needs spectral projections of `R`; it is proved in
`BookProof.ChapterResolventMinMaxEquality`, where the ladder becomes an equality at every
rung.  Nothing in
this chapter produces a spectral gap for any particular Hamiltonian: it converts a gap of
the resolvent's numerical ladder into a gap of the ladder of `T`.
-/

noncomputable section

namespace BookProof.ResolventLadder

open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open BookProof.NonnegResolvent BookProof.PositiveSquareRoot
open BookProof.NonnegSquareRoot BookProof.ClosureUniqueness
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. Cauchy–Schwarz for a non-negative bounded form -/

/-- A non-negative real quadratic polynomial has a non-positive discriminant. -/
theorem sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C) : B ^ 2 ≤ A * C := by
  have hA : 0 ≤ A := by simpa using h 0
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · -- `C = 0`: then `B = 0`.
    have hB : B = 0 := by
      by_contra hB
      have hlin : ∀ t : ℝ, 0 ≤ A + 2 * t * B := by
        intro t
        have := h t
        rw [← hC0] at this
        simpa using this
      have hval : 2 * (-(A + 1) / (2 * B)) * B = -(A + 1) := by field_simp
      have hkey := hlin (-(A + 1) / (2 * B))
      rw [hval] at hkey
      linarith
    rw [hB, ← hC0]
    simp
  · have hkey := h (-B / C)
    have hexp : A + 2 * (-B / C) * B + (-B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp
      ring
    rw [hexp] at hkey
    have hd : B ^ 2 / C ≤ A := by linarith
    calc B ^ 2 = B ^ 2 / C * C := by field_simp
      _ ≤ A * C := mul_le_mul_of_nonneg_right hd hCpos.le

/-- For a self-adjoint operator the real part of the form is symmetric. -/
theorem re_inner_symm_of_selfAdjoint {R : F →L[ℂ] F} (hsa : IsSelfAdjoint R) (x y : F) :
    (inner ℂ x (R y) : ℂ).re = (inner ℂ y (R x) : ℂ).re := by
  have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) y x
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← h, ← inner_conj_symm, Complex.conj_re]

/-- **Cauchy–Schwarz for the non-negative form `(u, v) ↦ Re⟪u, R v⟫`.** -/
theorem posForm_cauchy_schwarz {R : F →L[ℂ] F} (hsa : IsSelfAdjoint R)
    (hpos : ∀ x : F, 0 ≤ (inner ℂ x (R x) : ℂ).re) (x y : F) :
    ((inner ℂ x (R y) : ℂ).re) ^ 2 ≤ (inner ℂ x (R x) : ℂ).re * (inner ℂ y (R y) : ℂ).re := by
  refine sq_le_mul_of_quadratic_nonneg (hpos y) fun t => ?_
  have hsymm := re_inner_symm_of_selfAdjoint hsa x y
  have hexp : (inner ℂ (x + (t : ℂ) • y) (R (x + (t : ℂ) • y)) : ℂ).re
      = (inner ℂ x (R x) : ℂ).re + 2 * t * (inner ℂ x (R y) : ℂ).re
        + t ^ 2 * (inner ℂ y (R y) : ℂ).re := by
    rw [map_add, ContinuousLinearMap.map_smul, inner_add_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_ofReal,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [hsymm]
    ring
  have hnn := hpos (x + (t : ℂ) • y)
  rw [hexp] at hnn
  exact hnn

/-- `‖Rx‖⁴ ≤ ⟪x, Rx⟫ · ⟪Rx, R(Rx)⟫`: the Cauchy–Schwarz inequality at the pair
`(x, R x)`. -/
theorem normSq_sq_le_rayleigh_mul {R : F →L[ℂ] F} (hsa : IsSelfAdjoint R)
    (hpos : ∀ x : F, 0 ≤ (inner ℂ x (R x) : ℂ).re) (x : F) :
    ‖R x‖ ^ 4 ≤ rayleighVal R x * rayleighVal R (R x) := by
  have hmid : (inner ℂ x (R (R x)) : ℂ).re = ‖R x‖ ^ 2 := by
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) x (R x)
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← h, inner_self_eq_norm_sq_to_K]
    norm_cast
  have h := posForm_cauchy_schwarz hsa hpos x (R x)
  rw [hmid] at h
  calc ‖R x‖ ^ 4 = (‖R x‖ ^ 2) ^ 2 := by ring
    _ ≤ rayleighVal R x * rayleighVal R (R x) := h

/-! ## 2. The resolvent at `1` of a non-negative self-adjoint relation -/

variable {T : Submodule ℂ (F × F)}

/-- The resolvent `R = (T + 1)⁻¹` of a non-negative self-adjoint relation. -/
def res (hT : IsNonnegSelfAdjoint T) : F →L[ℂ] F := invCLMAt hT (a := 1) one_pos

theorem res_mem (hT : IsNonnegSelfAdjoint T) (h : F) : (res hT h, h - res hT h) ∈ T := by
  have := invCLMAt_mem hT (a := 1) one_pos h
  simpa [res] using this

theorem res_eq_of_mem (hT : IsNonnegSelfAdjoint T) {y z : F} (hyz : (y, z) ∈ T) :
    res hT (y + z) = y := by
  refine invCLMAt_eq_of_mem hT (a := 1) one_pos ?_
  simpa using hyz

theorem res_isSelfAdjoint (hT : IsNonnegSelfAdjoint T) : IsSelfAdjoint (res hT) :=
  isSelfAdjoint_invCLMAt hT one_pos

theorem res_re_inner_nonneg (hT : IsNonnegSelfAdjoint T) (x : F) : 0 ≤ rayleighVal (res hT) x := by
  have hre : 0 ≤ (inner ℂ (res hT x) (x - res hT x) : ℂ).re := hT.nonneg _ (res_mem hT x)
  have hsplit : (inner ℂ (res hT x) (x - res hT x) : ℂ).re
      = (inner ℂ (res hT x) x : ℂ).re - ‖res hT x‖ ^ 2 := by
    rw [inner_sub_right, Complex.sub_re, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hsymm : (inner ℂ x (res hT x) : ℂ).re = (inner ℂ (res hT x) x : ℂ).re := by
    rw [← inner_conj_symm, Complex.conj_re]
  have hnn : (0:ℝ) ≤ ‖res hT x‖ ^ 2 := sq_nonneg _
  rw [rayleighVal, hsymm]
  linarith [hsplit ▸ hre]

/-- Single-valuedness of the relation: an operator has at most one value at each point. -/
theorem graph_unique (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {y z z' : F}
    (h : (y, z) ∈ T) (h' : (y, z') ∈ T) : z = z' := by
  have hsub : ((0 : F), z - z') ∈ T := by
    have := T.sub_mem h h'
    simpa using this
  exact sub_eq_zero.mp (hsv _ hsub)

theorem res_injective (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) :
    Function.Injective (res hT) := by
  intro a b hab
  have h0 : res hT (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hmem := res_mem hT (a - b)
  rw [h0] at hmem
  have := hsv _ (by simpa using hmem)
  exact sub_eq_zero.1 this

/-! ## 3. The pointwise ladder inequality -/

/-- **The pointwise ladder inequality**: for `(y, z)` on the graph of `T`,
`‖y‖⁴ ≤ (‖y‖² + Re⟪y, z⟫) · Re⟪y, R y⟫`.  It is the operator form of the convexity of
`λ ↦ 1/(1 + λ)`, and it is proved by Cauchy–Schwarz for the non-negative form of `R`. -/
theorem normSq_sq_le_rayleigh_graph (hT : IsNonnegSelfAdjoint T) {y z : F} (hyz : (y, z) ∈ T) :
    ‖y‖ ^ 4 ≤ (‖y‖ ^ 2 + (inner ℂ y z : ℂ).re) * rayleighVal (res hT) y := by
  have hx : res hT (y + z) = y := res_eq_of_mem hT hyz
  have hmain := normSq_sq_le_rayleigh_mul (res_isSelfAdjoint hT) (res_re_inner_nonneg hT) (y + z)
  rw [hx] at hmain
  have hA : rayleighVal (res hT) (y + z) = ‖y‖ ^ 2 + (inner ℂ y z : ℂ).re := by
    rw [rayleighVal, hx, inner_add_left, Complex.add_re, inner_self_eq_norm_sq_to_K]
    have hzy : (inner ℂ z y : ℂ).re = (inner ℂ y z : ℂ).re := by
      rw [← inner_conj_symm, Complex.conj_re]
    rw [hzy]
    norm_cast
  rw [hA] at hmain
  exact hmain

/-- The unit-vector form: `1 ≤ (1 + Re⟪y, z⟫) · Re⟪y, R y⟫`. -/
theorem one_le_add_mul_rayleigh_of_unit (hT : IsNonnegSelfAdjoint T) {y z : F}
    (hyz : (y, z) ∈ T) (hy : ‖y‖ = 1) :
    1 ≤ (1 + (inner ℂ y z : ℂ).re) * rayleighVal (res hT) y := by
  have h := normSq_sq_le_rayleigh_graph hT hyz
  rw [hy] at h
  simpa using h

/-- If the resolvent's Rayleigh quotient at a unit vector of the domain is at most `c > 0`,
then the Rayleigh quotient of `T` there is at least `1/c − 1`. -/
theorem inv_sub_one_le_of_rayleigh_le (hT : IsNonnegSelfAdjoint T) {y z : F}
    (hyz : (y, z) ∈ T) (hy : ‖y‖ = 1) {c : ℝ} (hc : 0 < c)
    (hle : rayleighVal (res hT) y ≤ c) : 1 / c - 1 ≤ (inner ℂ y z : ℂ).re := by
  have hg : 0 ≤ (inner ℂ y z : ℂ).re := hT.nonneg _ hyz
  have h1 := one_le_add_mul_rayleigh_of_unit hT hyz hy
  have h2 : (1 + (inner ℂ y z : ℂ).re) * rayleighVal (res hT) y
      ≤ (1 + (inner ℂ y z : ℂ).re) * c :=
    mul_le_mul_of_nonneg_left hle (by linarith)
  have h3 : 1 / c ≤ 1 + (inner ℂ y z : ℂ).re := by
    rw [div_le_iff₀ hc]
    linarith
  linarith

/-! ## 4. The ladder of a bounded operator, read from the top -/

/-- The bottom of the numerical range of `R` on a subspace. -/
def rayleighInfOn (R : F →L[ℂ] F) (S : Submodule ℂ F) : ℝ := sInf (rayleighSetOn R S)

/-- The values `inf_{x ∈ S, ‖x‖ = 1} ⟪x, Rx⟫` over the `(k+1)`-dimensional subspaces. -/
def maxminSet (R : F →L[ℂ] F) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F, Module.finrank ℂ S = k + 1 ∧ t = rayleighInfOn R S}

/-- The `k`-th Courant–Fischer level of a bounded operator, **counted from the top**. -/
def maxminLevel (R : F →L[ℂ] F) (k : ℕ) : ℝ := sSup (maxminSet R k)

theorem rayleighSetOn_bddBelow (R : F →L[ℂ] F) (S : Submodule ℂ F) :
    BddBelow (rayleighSetOn R S) := by
  refine ⟨-‖R‖, ?_⟩
  rintro t ⟨x, -, hx1, rfl⟩
  exact neg_norm_le_rayleighVal_of_unit R hx1

theorem rayleighInfOn_le_norm (R : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : rayleighInfOn R S ≤ ‖R‖ := by
  obtain ⟨x, hx, hx1⟩ := exists_unit_mem S hS
  refine csInf_le_of_le (rayleighSetOn_bddBelow R S) (b := rayleighVal R x) ⟨x, hx, hx1, rfl⟩ ?_
  exact rayleighVal_le_norm_of_unit R hx1

theorem maxminSet_bddAbove (R : F →L[ℂ] F) (k : ℕ) : BddAbove (maxminSet R k) := by
  refine ⟨‖R‖, ?_⟩
  rintro t ⟨S, hrank, rfl⟩
  exact rayleighInfOn_le_norm R (by rw [hrank]; omega)

theorem rayleighInfOn_le_maxminLevel (R : F →L[ℂ] F) {S : Submodule ℂ F} {k : ℕ}
    (hrank : Module.finrank ℂ S = k + 1) : rayleighInfOn R S ≤ maxminLevel R k :=
  le_csSup (maxminSet_bddAbove R k) ⟨S, hrank, rfl⟩

/-- Below the level plus `ε` there is a unit vector of every competitor subspace. -/
theorem exists_unit_rayleigh_lt (R : F →L[ℂ] F) {S : Submodule ℂ F} {k : ℕ}
    (hrank : Module.finrank ℂ S = k + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, ‖x‖ = 1 ∧ rayleighVal R x < maxminLevel R k + ε := by
  have hpos : 0 < Module.finrank ℂ S := by rw [hrank]; omega
  have hne := rayleighSetOn_nonempty R hpos
  have hle := rayleighInfOn_le_maxminLevel R hrank
  have hlt : sInf (rayleighSetOn R S) < maxminLevel R k + ε := by
    have : rayleighInfOn R S = sInf (rayleighSetOn R S) := rfl
    linarith [this ▸ hle]
  obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨x, hx, hx1, rfl⟩ := ht
  exact ⟨x, hx, hx1, htlt⟩

theorem rayleighInfOn_span_singleton (R : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    rayleighInfOn R (Submodule.span ℂ {x}) = rayleighVal R x := by
  rw [rayleighInfOn, rayleighSetOn_span_singleton R hx1, csInf_singleton]

/-- The top rung of the ladder ranges over the Rayleigh quotients of the unit vectors. -/
theorem maxminSet_zero_eq_rayleighSet (R : F →L[ℂ] F) : maxminSet R 0 = rayleighSet R := by
  ext t
  constructor
  · rintro ⟨S, hrank, rfl⟩
    have hfd : FiniteDimensional ℂ S := .of_finrank_pos (by rw [hrank]; omega)
    obtain ⟨x, hx, hx1⟩ := exists_unit_mem S (by rw [hrank]; omega)
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx1
      simp at hx1
    have hspan : Submodule.span ℂ {x} = S :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (by simpa using hx))
        (by rw [finrank_span_singleton hx0, hrank])
    rw [← hspan, rayleighInfOn_span_singleton R hx1]
    exact ⟨x, hx1, rfl⟩
  · rintro ⟨x, hx1, rfl⟩
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx1
      simp at hx1
    exact ⟨Submodule.span ℂ {x}, by simpa using finrank_span_singleton hx0,
      (rayleighInfOn_span_singleton R hx1).symm⟩

theorem maxminLevel_zero_eq_sSup_rayleighSet (R : F →L[ℂ] F) :
    maxminLevel R 0 = sSup (rayleighSet R) := by
  rw [maxminLevel, maxminSet_zero_eq_rayleighSet]

theorem rayleighSet_bddAbove (R : F →L[ℂ] F) : BddAbove (rayleighSet R) := by
  refine ⟨‖R‖, ?_⟩
  rintro t ⟨x, hx1, rfl⟩
  exact rayleighVal_le_norm_of_unit R hx1

theorem rayleighSet_neg (R : F →L[ℂ] F) : rayleighSet (-R) = -rayleighSet R := by
  ext t
  rw [Set.mem_neg]
  constructor
  · rintro ⟨x, hx1, rfl⟩
    refine ⟨x, hx1, ?_⟩
    simp
  · rintro ⟨x, hx1, hx⟩
    refine ⟨x, hx1, ?_⟩
    have : (inner ℂ x ((-R) x) : ℂ).re = -(inner ℂ x (R x) : ℂ).re := by simp
    rw [this, ← hx, neg_neg]

/-- **The top of the numerical range is the top of the spectrum**, the mirror image of
`sInf_spectrum_eq_rayleighInf`. -/
theorem sSup_rayleighSet_eq_sSup_spectrum [Nontrivial F] (R : F →L[ℂ] F)
    (hR : IsSelfAdjoint R) : sSup (rayleighSet R) = sSup (spectrum ℝ R) := by
  have h := sInf_spectrum_eq_rayleighInf (-R) hR.neg
  rw [← spectrum.neg_eq, rayleighInf, rayleighSet_neg, Real.sInf_neg, Real.sInf_neg] at h
  linarith

/-! ## 5. The ladder of the relation -/

/-- The Rayleigh values of `T` at the unit vectors of a subspace of its domain. -/
def graphRayleighSet (T : Submodule ℂ (F × F)) (S : Submodule ℂ F) : Set ℝ :=
  {t : ℝ | ∃ y z : F, (y, z) ∈ T ∧ y ∈ S ∧ ‖y‖ = 1 ∧ t = (inner ℂ y z : ℂ).re}

/-- The top of the numerical range of `T` on a subspace of its domain. -/
def graphRayleighSup (T : Submodule ℂ (F × F)) (S : Submodule ℂ F) : ℝ :=
  sSup (graphRayleighSet T S)

/-- A subspace inside the domain of the relation. -/
def InDomain (T : Submodule ℂ (F × F)) (S : Submodule ℂ F) : Prop := ∀ y ∈ S, ∃ z, (y, z) ∈ T

/-- The values `sup_{y ∈ S, ‖y‖ = 1} ⟪y, Ty⟫` over the `(k+1)`-dimensional subspaces of the
domain. -/
def graphMinmaxSet (T : Submodule ℂ (F × F)) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F,
    Module.finrank ℂ S = k + 1 ∧ InDomain T S ∧ t = graphRayleighSup T S}

/-- The `k`-th Courant–Fischer level of the relation `T`. -/
def graphMinmaxLevel (T : Submodule ℂ (F × F)) (k : ℕ) : ℝ := sInf (graphMinmaxSet T k)

theorem graphRayleighSet_nonempty {S : Submodule ℂ F} (hS : 0 < Module.finrank ℂ S)
    (hdom : InDomain T S) : (graphRayleighSet T S).Nonempty := by
  obtain ⟨y, hy, hy1⟩ := exists_unit_mem S hS
  obtain ⟨z, hz⟩ := hdom y hy
  exact ⟨_, y, z, hz, hy, hy1, rfl⟩

theorem graphRayleighSet_nonneg (hT : IsNonnegSelfAdjoint T) {S : Submodule ℂ F} {t : ℝ}
    (ht : t ∈ graphRayleighSet T S) : 0 ≤ t := by
  obtain ⟨y, z, hyz, -, -, rfl⟩ := ht
  exact hT.nonneg _ hyz

theorem graphRayleighSup_nonneg (hT : IsNonnegSelfAdjoint T) (S : Submodule ℂ F) :
    0 ≤ graphRayleighSup T S :=
  Real.sSup_nonneg fun _ ht => graphRayleighSet_nonneg hT ht

/-- **A closed operator is bounded on a finite-dimensional subspace of its domain**, so the
Rayleigh values there are bounded above. -/
theorem graphRayleighSet_bddAbove (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0)
    {S : Submodule ℂ F} [FiniteDimensional ℂ S] (hdom : InDomain T S) :
    BddAbove (graphRayleighSet T S) := by
  classical
  have hchoose : ∀ y : S, ∃ z : F, ((y : F), z) ∈ T := fun y => hdom (y : F) y.2
  choose f hf using hchoose
  have hadd : ∀ a b : S, f (a + b) = f a + f b := by
    intro a b
    refine graph_unique hsv (hf (a + b)) ?_
    have := T.add_mem (hf a) (hf b)
    simpa using this
  have hsmul : ∀ (c : ℂ) (a : S), f (c • a) = c • f a := by
    intro c a
    refine graph_unique hsv (hf (c • a)) ?_
    have := T.smul_mem c (hf a)
    simpa using this
  let L : S →ₗ[ℂ] F :=
    { toFun := f
      map_add' := hadd
      map_smul' := by
        intro c a
        simpa using hsmul c a }
  let Lc : S →L[ℂ] F := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖, ?_⟩
  rintro t ⟨y, z, hyz, hyS, hy1, rfl⟩
  have hz : z = f ⟨y, hyS⟩ := graph_unique hsv hyz (hf ⟨y, hyS⟩)
  have hnorm : ‖f ⟨y, hyS⟩‖ ≤ ‖Lc‖ := by
    have hb := Lc.le_opNorm ⟨y, hyS⟩
    have hy' : ‖(⟨y, hyS⟩ : S)‖ = 1 := by simpa using hy1
    rw [hy', mul_one] at hb
    simpa [Lc, L, LinearMap.toContinuousLinearMap] using hb
  calc (inner ℂ y z : ℂ).re ≤ ‖(inner ℂ y z : ℂ)‖ := Complex.re_le_norm _
    _ ≤ ‖y‖ * ‖z‖ := norm_inner_le_norm _ _
    _ = ‖z‖ := by rw [hy1, one_mul]
    _ ≤ ‖Lc‖ := by rw [hz]; exact hnorm

theorem graphMinmaxSet_bddBelow (hT : IsNonnegSelfAdjoint T) (k : ℕ) :
    BddBelow (graphMinmaxSet T k) := by
  refine ⟨0, ?_⟩
  rintro t ⟨S, -, -, rfl⟩
  exact graphRayleighSup_nonneg hT S

/-- The resolvent supplies subspaces of every dimension inside the domain. -/
theorem graphMinmaxSet_nonempty (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {k : ℕ} {W : Submodule ℂ F}
    (hW : Module.finrank ℂ W = k + 1) : (graphMinmaxSet T k).Nonempty := by
  classical
  set R : F →ₗ[ℂ] F := (res hT : F →ₗ[ℂ] F) with hR
  have hinj : Function.Injective R := res_injective hT hsv
  have hfd : FiniteDimensional ℂ W := .of_finrank_pos (by rw [hW]; omega)
  have hequiv : W ≃ₗ[ℂ] (W.map R) := Submodule.equivMapOfInjective R hinj W
  have hrank : Module.finrank ℂ (W.map R) = k + 1 := by
    rw [← hequiv.finrank_eq, hW]
  have hdom : InDomain T (W.map R) := by
    rintro y hy
    obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hy
    exact ⟨w - res hT w, res_mem hT w⟩
  exact ⟨_, W.map R, hrank, hdom, rfl⟩

/-! ## 6. The ladder inequality -/

/-- **The ladder of `T` is bounded below by the ladder of its resolvent**, on every
competitor subspace. -/
theorem le_graphRayleighSup (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {S : Submodule ℂ F} {k : ℕ}
    (hrank : Module.finrank ℂ S = k + 1) (hdom : InDomain T S) :
    1 / maxminLevel (res hT) k - 1 ≤ graphRayleighSup T S := by
  have hfd : FiniteDimensional ℂ S := .of_finrank_pos (by rw [hrank]; omega)
  have hbdd := graphRayleighSet_bddAbove hsv hdom
  have hsupnn := graphRayleighSup_nonneg hT S
  rcases le_or_gt (maxminLevel (res hT) k) 0 with hν | hν
  · have h1 : 1 / maxminLevel (res hT) k ≤ 0 := by
      rcases eq_or_lt_of_le hν with h | h
      · rw [h]; simp
      · exact (one_div_neg.mpr h).le
    linarith
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ν := maxminLevel (res hT) k with hνdef
    have hε : 0 < δ * ν ^ 2 := by positivity
    obtain ⟨y, hyS, hy1, hlt⟩ := exists_unit_rayleigh_lt (res hT) hrank hε
    obtain ⟨z, hz⟩ := hdom y hyS
    have hc : 0 < ν + δ * ν ^ 2 := by nlinarith
    have hle := inv_sub_one_le_of_rayleigh_le hT hz hy1 hc hlt.le
    have hmem : (inner ℂ y z : ℂ).re ∈ graphRayleighSet T S := ⟨y, z, hz, hyS, hy1, rfl⟩
    have hsup : (inner ℂ y z : ℂ).re ≤ graphRayleighSup T S := le_csSup hbdd hmem
    have harith : 1 / ν ≤ 1 / (ν + δ * ν ^ 2) + δ := by
      rw [div_add' _ _ _ (ne_of_gt hc), div_le_div_iff₀ hν hc]
      nlinarith
    linarith

/-- **The ladder inequality**: for every `k`,
`1 / maxminLevel R k − 1 ≤ graphMinmaxLevel T k`. -/
theorem resolvent_ladder_lower (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (k : ℕ)
    (hne : (graphMinmaxSet T k).Nonempty) :
    1 / maxminLevel (res hT) k - 1 ≤ graphMinmaxLevel T k := by
  refine le_csInf hne ?_
  rintro t ⟨S, hrank, hdom, rfl⟩
  exact le_graphRayleighSup hT hsv hrank hdom

/-! ## 7. The bottom rung: an equality -/

theorem maxminLevel_zero_pos [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) : 0 < maxminLevel (res hT) 0 := by
  obtain ⟨x0, hx0⟩ := exists_ne (0 : F)
  set x : F := ‖x0‖⁻¹ • x0 with hxdef
  have hx1 : ‖x‖ = 1 := by
    rw [hxdef, norm_smul]
    simp [norm_ne_zero_iff.mpr hx0]
  have hxne : x ≠ 0 := by
    intro h
    rw [h] at hx1
    simp at hx1
  have hpos : 0 < rayleighVal (res hT) x := by
    rcases eq_or_lt_of_le (res_re_inner_nonneg hT x) with h | h
    · exfalso
      have hmain := normSq_sq_le_rayleigh_mul (res_isSelfAdjoint hT) (res_re_inner_nonneg hT) x
      rw [← h, zero_mul] at hmain
      have hzero : res hT x = 0 := by
        have h4 : ‖res hT x‖ ^ 4 = 0 := le_antisymm hmain (by positivity)
        exact norm_eq_zero.mp ((pow_eq_zero_iff (n := 4) (by norm_num)).mp h4)
      exact hxne (res_injective hT hsv (by rw [hzero, map_zero] : res hT x = res hT 0))
    · exact h
  have hle : rayleighInfOn (res hT) (Submodule.span ℂ {x}) ≤ maxminLevel (res hT) 0 :=
    rayleighInfOn_le_maxminLevel (res hT) (by simpa using finrank_span_singleton hxne)
  rw [rayleighInfOn_span_singleton (res hT) hx1] at hle
  linarith

/-- **The bottom rung of the ladder is exactly the transformed top of the resolvent's
ladder.** -/
theorem graphMinmaxLevel_zero_eq [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) :
    graphMinmaxLevel T 0 = 1 / maxminLevel (res hT) 0 - 1 := by
  obtain ⟨x0, hx0⟩ := exists_ne (0 : F)
  have hne : (graphMinmaxSet T 0).Nonempty :=
    graphMinmaxSet_nonempty hT hsv (W := Submodule.span ℂ {x0})
      (by simpa using finrank_span_singleton hx0)
  refine le_antisymm ?_ (resolvent_ladder_lower hT hsv 0 hne)
  set ν := maxminLevel (res hT) 0 with hνdef
  have hνpos : 0 < ν := maxminLevel_zero_pos hT hsv
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- pick a unit vector nearly maximizing the resolvent's Rayleigh quotient
  set ε : ℝ := min (ν / 2) (δ * ν ^ 2 / 2) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
  have hεν : ε ≤ ν / 2 := min_le_left _ _
  have hεδ : ε ≤ δ * ν ^ 2 / 2 := min_le_right _ _
  have hsup : ν = sSup (rayleighSet (res hT)) := maxminLevel_zero_eq_sSup_rayleighSet (res hT)
  obtain ⟨t, ht, htlt⟩ : ∃ t ∈ rayleighSet (res hT), ν - ε < t := by
    refine exists_lt_of_lt_csSup (rayleighSet_nonempty (res hT)) ?_
    rw [← hsup]
    linarith
  obtain ⟨x, hx1, rfl⟩ := ht
  set A : ℝ := rayleighVal (res hT) x with hA
  have hAle : A ≤ ν := by
    rw [hsup]
    exact le_csSup (rayleighSet_bddAbove (res hT)) ⟨x, hx1, rfl⟩
  have hApos : 0 < A := by
    have : ν - ε < A := htlt
    linarith
  set y : F := res hT x with hy
  have hAle2 : A ≤ ‖y‖ := by
    calc A = (inner ℂ x y : ℂ).re := rfl
      _ ≤ ‖(inner ℂ x y : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ = ‖y‖ := by rw [hx1, one_mul]
  have hypos : 0 < ‖y‖ := lt_of_lt_of_le hApos hAle2
  have hyne : y ≠ 0 := norm_pos_iff.mp hypos
  -- the line through `y` is a competitor
  have hmemT : (y, x - y) ∈ T := res_mem hT x
  have hdom : InDomain T (Submodule.span ℂ {y}) := by
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨c • (x - y), T.smul_mem c hmemT⟩
  have hrank : Module.finrank ℂ (Submodule.span ℂ {y}) = 0 + 1 := by
    simpa using finrank_span_singleton hyne
  -- every Rayleigh value on that line equals `A/‖y‖² − 1`
  have hval : ∀ t ∈ graphRayleighSet T (Submodule.span ℂ {y}), t = A / ‖y‖ ^ 2 - 1 := by
    rintro t ⟨u, w, huw, huS, hu1, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp huS
    have hw : w = c • (x - y) := graph_unique hsv huw (T.smul_mem c hmemT)
    have hc2 : ‖c‖ ^ 2 * ‖y‖ ^ 2 = 1 := by
      have : ‖c • y‖ = 1 := hu1
      rw [norm_smul] at this
      nlinarith [norm_nonneg c, norm_nonneg y]
    have hbase : (inner ℂ y (x - y) : ℂ).re = A - ‖y‖ ^ 2 := by
      rw [inner_sub_right, Complex.sub_re, inner_self_eq_norm_sq_to_K]
      have hyx : (inner ℂ y x : ℂ).re = A := by
        rw [hA, rayleighVal, ← hy, ← inner_conj_symm, Complex.conj_re]
      rw [hyx]
      norm_cast
    have hcc : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have hexp : (inner ℂ (c • y) w : ℂ).re = ‖c‖ ^ 2 * (inner ℂ y (x - y) : ℂ).re := by
      rw [hw, inner_smul_left, inner_smul_right, ← mul_assoc, hcc, Complex.re_ofReal_mul]
    rw [hexp, hbase]
    field_simp
    nlinarith [hc2]
  have hbdd : BddAbove (graphRayleighSet T (Submodule.span ℂ {y})) := by
    have : FiniteDimensional ℂ (Submodule.span ℂ {y}) := .of_finrank_pos (by rw [hrank]; omega)
    exact graphRayleighSet_bddAbove hsv hdom
  have hsetne : (graphRayleighSet T (Submodule.span ℂ {y})).Nonempty :=
    graphRayleighSet_nonempty (by rw [hrank]; omega) hdom
  have hsupval : graphRayleighSup T (Submodule.span ℂ {y}) ≤ A / ‖y‖ ^ 2 - 1 :=
    csSup_le hsetne fun t ht => le_of_eq (hval t ht)
  have hlow : graphMinmaxLevel T 0 ≤ graphRayleighSup T (Submodule.span ℂ {y}) :=
    csInf_le (graphMinmaxSet_bddBelow hT 0) ⟨_, hrank, hdom, rfl⟩
  -- arithmetic: `A/‖y‖² ≤ 1/A ≤ 1/(ν − ε) ≤ 1/ν + δ`
  have h1 : A / ‖y‖ ^ 2 ≤ 1 / A := by
    rw [div_le_div_iff₀ (by positivity) hApos]
    nlinarith [hAle2, hApos]
  have hAeq : (inner ℂ x y : ℂ).re = A := rfl
  have h2 : 1 / A ≤ 1 / (ν - ε) := by
    have hνε : 0 < ν - ε := by linarith
    exact one_div_le_one_div_of_le hνε (by rw [← hAeq]; linarith [htlt])
  have h3 : 1 / (ν - ε) ≤ 1 / ν + δ := by
    have hνε : 0 < ν - ε := by linarith
    rw [div_add' _ _ _ (ne_of_gt hνpos), div_le_div_iff₀ hνε hνpos]
    nlinarith
  linarith

/-- **The bottom rung, spectrally**: the lowest min–max level of `T` is determined by the
**top of the spectrum of its resolvent**. -/
theorem graphMinmaxLevel_zero_eq_sSup_spectrum [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) :
    graphMinmaxLevel T 0 = 1 / sSup (spectrum ℝ (res hT)) - 1 := by
  rw [graphMinmaxLevel_zero_eq hT hsv, maxminLevel_zero_eq_sSup_rayleighSet,
    sSup_rayleighSet_eq_sSup_spectrum (res hT) (res_isSelfAdjoint hT)]

/-! ## 8. The gap -/

/-- **A gap of the resolvent's ladder is a gap of the ladder of `T`.** -/
theorem graphMinmax_gap_lower [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0)
    (hne : (graphMinmaxSet T 1).Nonempty) :
    1 / maxminLevel (res hT) 1 - 1 / maxminLevel (res hT) 0
      ≤ graphMinmaxLevel T 1 - graphMinmaxLevel T 0 := by
  have h1 := resolvent_ladder_lower hT hsv 1 hne
  have h0 := graphMinmaxLevel_zero_eq hT hsv
  linarith

/-- **A strict gap of the resolvent's ladder gives a strictly positive gap for `T`.** -/
theorem graphMinmax_gap_pos [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0)
    (hne : (graphMinmaxSet T 1).Nonempty)
    (hgap : maxminLevel (res hT) 1 < maxminLevel (res hT) 0)
    (hpos : 0 < maxminLevel (res hT) 1) :
    0 < graphMinmaxLevel T 1 - graphMinmaxLevel T 0 := by
  have hlow := graphMinmax_gap_lower hT hsv hne
  have hstrict : 1 / maxminLevel (res hT) 0 < 1 / maxminLevel (res hT) 1 :=
    one_div_lt_one_div_of_lt hpos hgap
  linarith

/-! ## 9. What the numerics computes: the Galerkin levels of the resolvent

The shift-invert schemes of the project diagonalise finite compressions of the **resolvent**,
not of the Hamiltonian.  This section transports the Galerkin convergence theorem of
`ChapterSirkRitzMinMax` to the ladder read from the top (by applying it to `−R`), and turns a
computed Ritz level into a rigorous upper bound for the ground level of the unbounded
operator. -/

/-- The levels of `R` from the top, computed only inside a fixed subspace `W`: the Ritz
levels the solver produces from the truncation to `W`. -/
def maxminSetIn (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F, S ≤ W ∧ Module.finrank ℂ S = k + 1 ∧ t = rayleighInfOn R S}

/-- The `k`-th Rayleigh–Ritz level of the truncation of `R` to `W`, counted from the top. -/
def maxminLevelIn (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : ℝ := sSup (maxminSetIn R W k)

theorem rayleighVal_neg (R : F →L[ℂ] F) (x : F) : rayleighVal (-R) x = -rayleighVal R x := by
  simp [rayleighVal]

theorem rayleighSetOn_neg (R : F →L[ℂ] F) (S : Submodule ℂ F) :
    rayleighSetOn (-R) S = -rayleighSetOn R S := by
  ext t
  rw [Set.mem_neg]
  constructor
  · rintro ⟨x, hx, hx1, rfl⟩
    exact ⟨x, hx, hx1, by rw [rayleighVal_neg, neg_neg]⟩
  · rintro ⟨x, hx, hx1, hval⟩
    exact ⟨x, hx, hx1, by rw [rayleighVal_neg, ← hval, neg_neg]⟩

theorem rayleighSup_neg (R : F →L[ℂ] F) (S : Submodule ℂ F) :
    rayleighSup (-R) S = -rayleighInfOn R S := by
  rw [rayleighSup, rayleighSetOn_neg, Real.sSup_neg, rayleighInfOn]

theorem minmaxSet_neg (R : F →L[ℂ] F) (k : ℕ) : minmaxSet (-R) k = -maxminSet R k := by
  ext t
  rw [Set.mem_neg]
  constructor
  · rintro ⟨S, hrank, rfl⟩
    exact ⟨S, hrank, by rw [rayleighSup_neg, neg_neg]⟩
  · rintro ⟨S, hrank, hval⟩
    exact ⟨S, hrank, by rw [rayleighSup_neg, ← hval, neg_neg]⟩

/-- The ladder from the top is the ladder of `−R` from the bottom. -/
theorem minmaxLevel_neg (R : F →L[ℂ] F) (k : ℕ) :
    minmaxLevel (-R) k = -maxminLevel R k := by
  rw [minmaxLevel, minmaxSet_neg, Real.sInf_neg, maxminLevel]

theorem minmaxSetIn_neg (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    minmaxSetIn (-R) W k = -maxminSetIn R W k := by
  ext t
  rw [Set.mem_neg]
  constructor
  · rintro ⟨S, hle, hrank, rfl⟩
    exact ⟨S, hle, hrank, by rw [rayleighSup_neg, neg_neg]⟩
  · rintro ⟨S, hle, hrank, hval⟩
    exact ⟨S, hle, hrank, by rw [rayleighSup_neg, ← hval, neg_neg]⟩

theorem minmaxLevelIn_neg (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    minmaxLevelIn (-R) W k = -maxminLevelIn R W k := by
  rw [minmaxLevelIn, minmaxSetIn_neg, Real.sInf_neg, maxminLevelIn]

/-- **The variational principle for the ladder from the top**: a computed Ritz level is a
**lower** bound for the true level. -/
theorem maxminLevelIn_le_maxminLevel (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (maxminSetIn R W k).Nonempty) : maxminLevelIn R W k ≤ maxminLevel R k := by
  have hne' : (minmaxSetIn (-R) W k).Nonempty := by
    rw [minmaxSetIn_neg]
    obtain ⟨t, ht⟩ := hne
    exact ⟨-t, by rwa [Set.mem_neg, neg_neg]⟩
  have h := minmaxLevel_le_minmaxLevelIn (-R) W k hne'
  rw [minmaxLevel_neg, minmaxLevelIn_neg] at h
  linarith

/-- **The Galerkin levels of the resolvent converge to its Courant–Fischer levels from the
top.** -/
theorem galerkin_maxminLevel_tendsto (R : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) :
    Tendsto (fun m : ℕ => maxminLevelIn R (galerkinSpan b m) k) atTop
      (nhds (maxminLevel R k)) := by
  have h := galerkin_minmaxLevel_tendsto (-R) b k
  simp only [minmaxLevel_neg, minmaxLevelIn_neg] at h
  simpa using h.neg

/-- **A gap of the resolvent's ladder is eventually seen by the truncations.** -/
theorem galerkin_maxmin_gap_eventually_pos (R : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    (hgap : maxminLevel R 1 < maxminLevel R 0) :
    ∀ᶠ m : ℕ in atTop, 0 < maxminLevelIn R (galerkinSpan b m) 0
      - maxminLevelIn R (galerkinSpan b m) 1 :=
  (((galerkin_maxminLevel_tendsto R b 0).sub
    (galerkin_maxminLevel_tendsto R b 1)).eventually_const_lt (by linarith))

/-- **A computed Ritz level of the resolvent bounds the ground level of the unbounded
operator.**  Whatever finite subspace the solver retains, the level it computes there is a
lower bound for the top of the resolvent's ladder, hence `1/(computed) − 1` is a rigorous
**upper** bound for the lowest min–max level of `T`. -/
theorem graphMinmaxLevel_zero_le_of_computed [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {W : Submodule ℂ F}
    (hne : (maxminSetIn (res hT) W 0).Nonempty)
    (hpos : 0 < maxminLevelIn (res hT) W 0) :
    graphMinmaxLevel T 0 ≤ 1 / maxminLevelIn (res hT) W 0 - 1 := by
  have hle := maxminLevelIn_le_maxminLevel (res hT) W 0 hne
  have hinv : 1 / maxminLevel (res hT) 0 ≤ 1 / maxminLevelIn (res hT) W 0 :=
    one_div_le_one_div_of_le hpos hle
  rw [graphMinmaxLevel_zero_eq hT hsv]
  linarith

end BookProof.ResolventLadder

end


