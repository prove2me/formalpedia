-- Prove2me | Definitions.Def_ChapterPolarPartialIsometry
-- name    : ChapterPolarPartialIsometry
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T12:14:19.732747+00:00
-- url     : https://prove2.me/theorems/1de9cdd4-82bf-49b5-a110-5eff63ae40ae
-- title:
--   The Lean 4 theorem `isClosed_initSpace` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPolarPartialIsometry.lean`): generated def bundle for ChapterPolarPartialIsometry. See BookProof/ChapterPolarPartialIsometry.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPolarPartialIsometry.lean

import Theorems.Thm_BookProof_ClosureUniqueness_exists_linearIsometry_of_inner_eq


import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterVonNeumannCore
import Definitions.Def_ChapterUnboundedPolar
import Mathlib


/-!
# The polar decomposition as a genuine partial isometry, and its uniqueness

`BookProof.ChapterUnboundedPolar` proves `|Ā| = (A* Ā)^{1/2}`, `D(|Ā|) = D(Ā)`,
`‖ |Ā| x ‖ = ‖Ā x‖`, and — as an existence statement — a linear isometry `U` from
`ran |Ā|` onto `ran Ā` with `U (|Ā| x) = Ā x` (`exists_polar_isometry`).  That `U`
is only defined on the (not necessarily closed) range of `|Ā|`, it is not an
operator on `F`, and nothing is said about its uniqueness.

This module upgrades it to the classical statement.  Everything is done for a
general pair of linear maps with the same sesquilinear form and then applied.

## What is proved

Part 1 — the abstract construction.  For `P Q : Dom →ₗ[ℂ] F` with
`⟪P x, P y⟫ = ⟪Q x, Q y⟫` (equivalently `P* P = Q* Q`), write
`initSpace P = closure (ran P)`.  Then there is a **continuous** operator
`polarIsom P Q : F →L[ℂ] F` with

* `polarIsom_apply_range` : `U (P x) = Q x`;
* `norm_polarIsom` : `‖U z‖ = ‖p z‖` for every `z`, where `p` is the orthogonal
  projection onto `initSpace P` — so `U` is a **partial isometry** with initial
  space `closure (ran P)`;
* `polarIsom_eq_zero_of_mem_orthogonal` : `U` kills `(initSpace P)ᗮ`;
* `inner_polarIsom` and `adjoint_comp_polarIsom` : `U* U = p`;
* `polarIsom_mem_initSpace` and `polarIsom_comp_adjoint` : `U` maps into
  `closure (ran Q)` and `U U*` is the projection onto it — the final space;
* `adjoint_polarIsom_apply` : `U* (Q x) = P x`;
* `polarIsom_unique` : those two properties determine `U`.

Part 2 — the application to `Ā`.  `polarU A` is the partial isometry of the polar
decomposition of the closure `Ā`:

* **`polarU_absOn`** : `Ā x = U |Ā| x` — the polar decomposition;
* **`adjoint_polarU_clExt`** : `|Ā| x = U* Ā x`;
* `norm_polarU`, `polarU_eq_zero_of_mem_orthogonal`, `adjoint_comp_polarU`
  (`U* U` is the projection onto `closure (ran |Ā|)`) and `polarU_comp_adjoint`
  (`U U*` is the projection onto `closure (ran Ā)`);
* **`polarU_unique`** : `U` is the unique bounded operator that decomposes `Ā`
  and vanishes on the orthogonal complement of `closure (ran |Ā|)`;
* `absOn_eq_zero_iff` : `|Ā| x = 0 ↔ Ā x = 0` (the kernels agree).

Hypotheses: `F` is a complex Hilbert space, `A` symmetric on a dense domain `D`.
No invariance of the domain is used.
-/

namespace BookProof.PolarPartialIsometry

open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.FriedrichsSquare BookProof.VonNeumannCore BookProof.UnboundedPolar

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {Dom : Submodule ℂ F}

/-! ## Part 1 — the abstract partial isometry -/

/-- The initial space of the partial isometry: the closure of `ran P`. -/
def initSpace (P : Dom →ₗ[ℂ] F) : Submodule ℂ F := (LinearMap.range P).topologicalClosure

theorem isClosed_initSpace (P : Dom →ₗ[ℂ] F) :
    IsClosed ((initSpace P : Submodule ℂ F) : Set F) :=
  Submodule.isClosed_topologicalClosure _

theorem range_le_initSpace (P : Dom →ₗ[ℂ] F) : LinearMap.range P ≤ initSpace P :=
  Submodule.le_topologicalClosure _

instance instCompleteSpaceInitSpace [CompleteSpace F] (P : Dom →ₗ[ℂ] F) :
    CompleteSpace (initSpace P) :=
  (isClosed_initSpace P).completeSpace_coe

section Abstract

variable (P Q : Dom →ₗ[ℂ] F)
  (h : ∀ x y : Dom, (inner ℂ (P x) (P y) : ℂ) = inner ℂ (Q x) (Q y))

/-- The isometry on `ran P` supplied by `ClosureUniqueness.exists_linearIsometry_of_inner_eq`. -/
noncomputable def preIsom : LinearMap.range P →ₗ[ℂ] F :=
  Classical.choose (exists_linearIsometry_of_inner_eq P Q h)

theorem preIsom_apply (x : Dom) :
    preIsom P Q h ⟨P x, LinearMap.mem_range_self P x⟩ = Q x :=
  (Classical.choose_spec (exists_linearIsometry_of_inner_eq P Q h)).1 x

theorem norm_preIsom (z : LinearMap.range P) : ‖preIsom P Q h z‖ = ‖(z : F)‖ :=
  (Classical.choose_spec (exists_linearIsometry_of_inner_eq P Q h)).2.1 z

/-- The same isometry, as a continuous linear map. -/
noncomputable def preIsomL : LinearMap.range P →L[ℂ] F :=
  (preIsom P Q h).mkContinuous 1 (by
    intro z
    rw [norm_preIsom, one_mul]
    rfl)

@[simp] theorem preIsomL_apply (z : LinearMap.range P) : preIsomL P Q h z = preIsom P Q h z := rfl

/-- The inclusion of `ran P` into its closure, as a continuous linear map. -/
noncomputable def inclL : LinearMap.range P →L[ℂ] initSpace P :=
  (Submodule.inclusion (range_le_initSpace P)).mkContinuous 1 (by intro z; simp)

@[simp] theorem inclL_coe (z : LinearMap.range P) : ((inclL P z : initSpace P) : F) = (z : F) := rfl

theorem norm_inclL (z : LinearMap.range P) : ‖inclL P z‖ = ‖z‖ := rfl

theorem isometry_inclL : Isometry (inclL P) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_inclL P)

theorem isUniformInducing_inclL : IsUniformInducing (inclL P) :=
  (isometry_inclL P).isUniformInducing

theorem denseRange_inclL : DenseRange (inclL P) := by
  intro z
  have hz : (z : F) ∈ closure ((LinearMap.range P : Submodule ℂ F) : Set F) := by
    have hz2 : (z : F) ∈ (LinearMap.range P).topologicalClosure := z.2
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hz2
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hz
  refine mem_closure_iff_seq_limit.2 ⟨fun n => inclL P ⟨u n, hu n⟩, fun n => ⟨_, rfl⟩, ?_⟩
  rw [tendsto_subtype_rng]
  exact hlim

variable [CompleteSpace F]

/-- **The partial isometry of the polar decomposition.** -/
noncomputable def polarIsom : F →L[ℂ] F :=
  ((preIsomL P Q h).extend (inclL P)).comp (initSpace P).orthogonalProjection

theorem polarIsom_apply (z : F) :
    polarIsom P Q h z = (preIsomL P Q h).extend (inclL P) ((initSpace P).orthogonalProjection z) :=
  rfl

/-- On the initial space the operator is the continuous extension of the isometry. -/
theorem polarIsom_apply_of_mem {z : F} (hz : z ∈ initSpace P) :
    polarIsom P Q h z = (preIsomL P Q h).extend (inclL P) ⟨z, hz⟩ := by
  rw [polarIsom_apply]
  congr 1
  exact Submodule.orthogonalProjection_mem_subspace_eq_self ⟨z, hz⟩

/-- **`U (P x) = Q x`.** -/
theorem polarIsom_apply_range (x : Dom) : polarIsom P Q h (P x) = Q x := by
  have hmem : P x ∈ initSpace P := range_le_initSpace P (LinearMap.mem_range_self P x)
  rw [polarIsom_apply_of_mem P Q h hmem]
  have hincl : inclL P ⟨P x, LinearMap.mem_range_self P x⟩ = ⟨P x, hmem⟩ := rfl
  rw [← hincl, ContinuousLinearMap.extend_eq _ (denseRange_inclL P) (isUniformInducing_inclL P),
    preIsomL_apply, preIsom_apply]

/-- The extension is isometric on the whole initial space. -/
theorem norm_extend (w : initSpace P) :
    ‖(preIsomL P Q h).extend (inclL P) w‖ = ‖w‖ := by
  refine (denseRange_inclL P).induction_on w ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro z
    rw [ContinuousLinearMap.extend_eq _ (denseRange_inclL P) (isUniformInducing_inclL P),
      preIsomL_apply, norm_preIsom, norm_inclL]
    rfl

/-- **`U` is isometric on the initial space.** -/
theorem norm_polarIsom_of_mem {z : F} (hz : z ∈ initSpace P) : ‖polarIsom P Q h z‖ = ‖z‖ := by
  rw [polarIsom_apply_of_mem P Q h hz, norm_extend]
  rfl

/-- **`U` kills the orthogonal complement of the initial space.** -/
theorem polarIsom_eq_zero_of_mem_orthogonal {z : F} (hz : z ∈ (initSpace P)ᗮ) :
    polarIsom P Q h z = 0 := by
  rw [polarIsom_apply,
    Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hz, map_zero]

/-- **`U` is a partial isometry**: `‖U z‖` is the norm of the projection of `z`
onto the initial space. -/
theorem norm_polarIsom (z : F) :
    ‖polarIsom P Q h z‖ = ‖(initSpace P).starProjection z‖ := by
  have hmem : (initSpace P).starProjection z ∈ initSpace P := by simp
  have hsplit : z - (initSpace P).starProjection z ∈ (initSpace P)ᗮ := by simp
  have h1 : polarIsom P Q h z = polarIsom P Q h ((initSpace P).starProjection z) := by
    have hz : z = (initSpace P).starProjection z + (z - (initSpace P).starProjection z) := by abel
    conv_lhs => rw [hz]
    rw [map_add, polarIsom_eq_zero_of_mem_orthogonal P Q h hsplit, add_zero]
  rw [h1, norm_polarIsom_of_mem P Q h hmem]

omit [CompleteSpace F] in
/-- Polarization for continuous operators: two operators with the same norms have
the same sesquilinear form. -/
theorem inner_eq_of_norm_eq_clm (S T : F →L[ℂ] F) (hnorm : ∀ z, ‖S z‖ = ‖T z‖) (z w : F) :
    (inner ℂ (S z) (S w) : ℂ) = inner ℂ (T z) (T w) := by
  have key : ∀ c : ℂ, ‖S z + c • S w‖ = ‖T z + c • T w‖ := by
    intro c
    have hS : S z + c • S w = S (z + c • w) := by rw [map_add, map_smul]
    have hT : T z + c • T w = T (z + c • w) := by rw [map_add, map_smul]
    rw [hS, hT, hnorm]
  have e1 : ‖S z + S w‖ = ‖T z + T w‖ := by simpa using key 1
  have e2 : ‖S z - S w‖ = ‖T z - T w‖ := by
    have := key (-1); simpa [sub_eq_add_neg] using this
  have e3 : ‖S z - (RCLike.I : ℂ) • S w‖ = ‖T z - (RCLike.I : ℂ) • T w‖ := by
    have := key (-(RCLike.I : ℂ)); simpa [sub_eq_add_neg] using this
  have e4 : ‖S z + (RCLike.I : ℂ) • S w‖ = ‖T z + (RCLike.I : ℂ) • T w‖ := key _
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4]

/-- `⟪U z, U w⟫ = ⟪p z, p w⟫`: the form of `U` is the projection. -/
theorem inner_polarIsom (z w : F) :
    (inner ℂ (polarIsom P Q h z) (polarIsom P Q h w) : ℂ)
      = inner ℂ ((initSpace P).starProjection z) ((initSpace P).starProjection w) :=
  inner_eq_of_norm_eq_clm _ _ (norm_polarIsom P Q h) z w

/-- **`U* U = p`**, the orthogonal projection onto the initial space. -/
theorem adjoint_comp_polarIsom :
    (ContinuousLinearMap.adjoint (polarIsom P Q h)).comp (polarIsom P Q h)
      = (initSpace P).starProjection := by
  refine ContinuousLinearMap.ext fun w => ?_
  refine ext_inner_left ℂ fun z => ?_
  have hidem : (initSpace P).starProjection ((initSpace P).starProjection w)
      = (initSpace P).starProjection w := Submodule.starProjection_eq_self_iff.2 (by simp)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_polarIsom P Q h, Submodule.inner_starProjection_left_eq_right, hidem]

/-- **`U* (Q x) = P x`.** -/
theorem adjoint_polarIsom_apply (x : Dom) :
    ContinuousLinearMap.adjoint (polarIsom P Q h) (Q x) = P x := by
  have h1 : Q x = polarIsom P Q h (P x) := (polarIsom_apply_range P Q h x).symm
  have h2 := congrArg (fun T : F →L[ℂ] F => T (P x)) (adjoint_comp_polarIsom P Q h)
  simp only [ContinuousLinearMap.comp_apply] at h2
  rw [h1, h2]
  exact Submodule.starProjection_eq_self_iff.2 (range_le_initSpace P (LinearMap.mem_range_self P x))

/-- **The final space.**  `U` maps into `closure (ran Q)`. -/
theorem polarIsom_mem_initSpace (z : F) : polarIsom P Q h z ∈ initSpace Q := by
  rw [polarIsom_apply]
  refine (denseRange_inclL P).induction_on ((initSpace P).orthogonalProjection z) ?_ ?_
  · exact IsClosed.preimage (map_continuous _) (isClosed_initSpace Q)
  · intro y
    obtain ⟨x, hx⟩ := y.2
    have hy : y = ⟨P x, LinearMap.mem_range_self P x⟩ := Subtype.ext hx.symm
    rw [ContinuousLinearMap.extend_eq _ (denseRange_inclL P) (isUniformInducing_inclL P), hy,
      preIsomL_apply, preIsom_apply]
    exact range_le_initSpace Q (LinearMap.mem_range_self Q x)

/-- **`U U* = q`**, the orthogonal projection onto the final space `closure (ran Q)`. -/
theorem polarIsom_comp_adjoint :
    (polarIsom P Q h).comp (ContinuousLinearMap.adjoint (polarIsom P Q h))
      = (initSpace Q).starProjection := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (polarIsom_mem_initSpace P Q h _) ?_).symm
  intro w hw
  have hzero : ∀ x : Dom,
      (inner ℂ (z - polarIsom P Q h (ContinuousLinearMap.adjoint (polarIsom P Q h) z))
        (Q x) : ℂ) = 0 := by
    intro x
    have hQ : Q x = polarIsom P Q h (P x) := (polarIsom_apply_range P Q h x).symm
    have hPx : (initSpace P).starProjection (P x) = P x :=
      Submodule.starProjection_eq_self_iff.2 (range_le_initSpace P (LinearMap.mem_range_self P x))
    have hUU : (inner ℂ (polarIsom P Q h (ContinuousLinearMap.adjoint (polarIsom P Q h) z))
        (polarIsom P Q h (P x)) : ℂ)
        = inner ℂ (ContinuousLinearMap.adjoint (polarIsom P Q h) z) (P x) := by
      have h2 := congrArg (fun T : F →L[ℂ] F => T (P x)) (adjoint_comp_polarIsom P Q h)
      simp only [ContinuousLinearMap.comp_apply] at h2
      rw [← ContinuousLinearMap.adjoint_inner_right, h2, hPx]
    rw [inner_sub_left, hQ, hUU, ContinuousLinearMap.adjoint_inner_left, sub_self]
  have hclosed : IsClosed {y : F | (inner ℂ
      (z - polarIsom P Q h (ContinuousLinearMap.adjoint (polarIsom P Q h) z)) y : ℂ) = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : ((LinearMap.range Q : Submodule ℂ F) : Set F)
      ⊆ {y : F | (inner ℂ
        (z - polarIsom P Q h (ContinuousLinearMap.adjoint (polarIsom P Q h) z)) y : ℂ) = 0} := by
    rintro y ⟨x, rfl⟩
    exact hzero x
  have hw' : w ∈ closure ((LinearMap.range Q : Submodule ℂ F) : Set F) := by
    have hw2 : w ∈ (LinearMap.range Q).topologicalClosure := hw
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hw2
  exact hclosed.closure_subset_iff.2 hsub hw'

/-- **Uniqueness.**  A bounded operator that decomposes `Q` through `P` and
vanishes on the orthogonal complement of `closure (ran P)` is `polarIsom P Q`. -/
theorem polarIsom_unique (V : F →L[ℂ] F) (hV : ∀ x : Dom, V (P x) = Q x)
    (hV0 : ∀ z ∈ (initSpace P)ᗮ, V z = 0) : V = polarIsom P Q h := by
  have hagree : ∀ y ∈ initSpace P, V y = polarIsom P Q h y := by
    have hclosed : IsClosed {y : F | V y = polarIsom P Q h y} :=
      isClosed_eq V.continuous (polarIsom P Q h).continuous
    have hsub : ((LinearMap.range P : Submodule ℂ F) : Set F)
        ⊆ {y : F | V y = polarIsom P Q h y} := by
      rintro y ⟨x, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [hV x, polarIsom_apply_range]
    intro y hy
    have hy' : y ∈ closure ((LinearMap.range P : Submodule ℂ F) : Set F) := by
      have hy2 : y ∈ (LinearMap.range P).topologicalClosure := hy
      rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hy2
    exact hclosed.closure_subset_iff.2 hsub hy'
  refine ContinuousLinearMap.ext fun z => ?_
  have hz : z = (initSpace P).starProjection z + (z - (initSpace P).starProjection z) := by abel
  have hmem : (initSpace P).starProjection z ∈ initSpace P := by simp
  have hperp : z - (initSpace P).starProjection z ∈ (initSpace P)ᗮ := by simp
  conv_lhs => rw [hz]
  conv_rhs => rw [hz]
  rw [map_add, map_add, hV0 _ hperp, polarIsom_eq_zero_of_mem_orthogonal P Q h hperp,
    hagree _ hmem]

end Abstract

/-! ## Part 2 — the polar decomposition of the closure `Ā` -/

section Application

variable [CompleteSpace F] {D : Submodule ℂ F} (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
  (hsym : SymmetricOn D A)

/-- **The partial isometry of the polar decomposition `Ā = U |Ā|`.** -/
noncomputable def polarU : F →L[ℂ] F :=
  polarIsom (absOn A hdense hsym) (clExt A hdense hsym) (inner_absOn A hdense hsym)

/-- **The polar decomposition `Ā = U |Ā|`.** -/
theorem polarU_absOn (x : clDom A) :
    polarU A hdense hsym (absOn A hdense hsym x) = clExt A hdense hsym x :=
  polarIsom_apply_range _ _ _ x

/-- **`|Ā| = U* Ā`.** -/
theorem adjoint_polarU_clExt (x : clDom A) :
    ContinuousLinearMap.adjoint (polarU A hdense hsym) (clExt A hdense hsym x)
      = absOn A hdense hsym x :=
  adjoint_polarIsom_apply _ _ _ x

/-- `U` is a partial isometry with initial space `closure (ran |Ā|)`. -/
theorem norm_polarU (z : F) :
    ‖polarU A hdense hsym z‖
      = ‖(initSpace (absOn A hdense hsym)).starProjection z‖ :=
  norm_polarIsom _ _ _ z

theorem polarU_eq_zero_of_mem_orthogonal {z : F}
    (hz : z ∈ (initSpace (absOn A hdense hsym))ᗮ) : polarU A hdense hsym z = 0 :=
  polarIsom_eq_zero_of_mem_orthogonal _ _ _ hz

/-- **`U* U` is the projection onto `closure (ran |Ā|)`.** -/
theorem adjoint_comp_polarU :
    (ContinuousLinearMap.adjoint (polarU A hdense hsym)).comp (polarU A hdense hsym)
      = (initSpace (absOn A hdense hsym)).starProjection :=
  adjoint_comp_polarIsom _ _ _

/-- **`U U*` is the projection onto `closure (ran Ā)`**, the final space. -/
theorem polarU_comp_adjoint :
    (polarU A hdense hsym).comp (ContinuousLinearMap.adjoint (polarU A hdense hsym))
      = (initSpace (clExt A hdense hsym)).starProjection :=
  polarIsom_comp_adjoint _ _ _

/-- **Uniqueness of the partial isometry of the polar decomposition.** -/
theorem polarU_unique (V : F →L[ℂ] F)
    (hV : ∀ x : clDom A, V (absOn A hdense hsym x) = clExt A hdense hsym x)
    (hV0 : ∀ z ∈ (initSpace (absOn A hdense hsym))ᗮ, V z = 0) : V = polarU A hdense hsym :=
  polarIsom_unique _ _ _ V hV hV0

/-- **The kernels agree**: `|Ā| x = 0 ↔ Ā x = 0`. -/
theorem absOn_eq_zero_iff (x : clDom A) :
    absOn A hdense hsym x = 0 ↔ clExt A hdense hsym x = 0 := by
  rw [← norm_eq_zero, ← norm_eq_zero (a := clExt A hdense hsym x), norm_absOn]

end Application

end BookProof.PolarPartialIsometry


