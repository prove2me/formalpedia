-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.finite_curve_degree_profile_span_of_smooth_projective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T14:21:56.665325+00:00
-- url     : https://prove2.me/submissions/633518d4-c439-4bf2-b9e1-dfcf413c6914
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_linear_realization_of_curve_degrees

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace PhilipponCohomologicalProfileRank

lemma finite_subfamily {A E ι : Type*} [Semiring A] [AddCommMonoid E] [Module A E]
    (f : ι → E) (hf : (Submodule.span A (Set.range f)).FG) :
    ∃ s : Finset ι, Submodule.span A (f '' (s : Set ι)) =
      Submodule.span A (Set.range f) := by
  classical
  obtain ⟨a, ha, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (Set.range f)).mp hf
  obtain ⟨s, _, hs, heq⟩ := a.finite_toSet.exists_subset_finite_image_eq
    (s := Set.univ) (by simpa using ha)
  refine ⟨hs.toFinset, ?_⟩
  simpa only [hs.coe_toFinset, heq] using hspan.symm

/-- Profiles over a subfield represented by linear functionals on a finite-dimensional
space have finite rank over that subfield, without assuming the field extension finite. -/
theorem finite_span_of_linear_realization
    {R F V α ι : Type*} [Field R] [Field F] [Algebra R F]
    [AddCommGroup V] [Module F V] [Module.Finite F V]
    (v : ι → V) (p : α → ι → R) (L : α → Module.Dual F V)
    (hp : ∀ a t, algebraMap R F (p a t) = L a (v t)) :
    Module.Finite R (Submodule.span R (Set.range p)) := by
  classical
  obtain ⟨s, hs⟩ := finite_subfamily (A := F) v (IsNoetherian.noetherian _)
  let U := Submodule.span R (Set.range p)
  have represent : ∀ u ∈ U, ∃ l : Module.Dual F V,
      ∀ t, algebraMap R F (u t) = l (v t) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨a, rfl⟩ := hu
      exact ⟨L a, hp a⟩
    | zero => exact ⟨0, by simp⟩
    | add u w hu hw ihu ihw =>
      obtain ⟨l, hl⟩ := ihu
      obtain ⟨m, hm⟩ := ihw
      exact ⟨l + m, fun t => by simp [hl t, hm t]⟩
    | smul a u hu ihu =>
      obtain ⟨l, hl⟩ := ihu
      refine ⟨algebraMap R F a • l, fun t => ?_⟩
      simp [smul_eq_mul, hl t, Algebra.smul_def]
  let e : U →ₗ[R] (s → R) :=
    { toFun := fun u t => u.val t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot]
    apply eq_bot_iff.mpr
    intro u hu
    obtain ⟨l, hl⟩ := represent u.val u.property
    have hz : ∀ w ∈ Submodule.span F (v '' (s : Set ι)), l w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨t, ht, rfl⟩ := hw
        rw [← hl t]
        have h := congrArg (fun f : s → R => f ⟨t, ht⟩)
          (show e u = 0 from hu)
        change u.val t = 0 at h
        rw [h, map_zero]
      | zero => simp
      | add w z hw hz ihw ihz => simp [ihw, ihz]
      | smul a w hw ih => simp [ih]
    change u = 0
    apply Subtype.ext
    funext t
    change u.val t = 0
    apply (algebraMap R F).injective
    rw [map_zero, hl t]
    apply hz
    rw [hs]
    exact Submodule.subset_span (Set.mem_range_self t)
  exact Module.Finite.of_injective e he

end PhilipponCohomologicalProfileRank

open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] [Smooth π]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    Module.Finite ℚ
      (Submodule.span ℚ (Set.range
        (fun M : {M : X.Modules // Scheme.Modules.IsInvertible M} =>
          (fun t : CurveDegreeTests.Probe π => (t.degree M.val : ℚ)))))  := by
  obtain ⟨F, hF, hchar, r, v, L, hdegree⟩ :=
    RelPicard.exists_finite_linear_realization_of_curve_degrees K π n i hi
  letI := hF
  letI := hchar
  exact PhilipponCohomologicalProfileRank.finite_span_of_linear_realization v
    (fun M : {M : X.Modules // Scheme.Modules.IsInvertible M} =>
      fun t : CurveDegreeTests.Probe π => (t.degree M.val : ℚ)) L hdegree
