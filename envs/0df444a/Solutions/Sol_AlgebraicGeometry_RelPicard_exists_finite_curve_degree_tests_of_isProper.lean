-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_finite_curve_degree_tests_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T16:20:24.883362+00:00
-- url     : https://prove2.me/submissions/5e84c6bb-63b3-4860-b119-052d7d9d3d61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_surjective_cover_of_isProper
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_curve_degree_tests_of_smooth_projective
import Theorems.Thm_AlgebraicGeometry_CurveDegreeTests_exists_curve_degree_multisection

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace AlgebraicGeometry.CurveDegreeTests.Descent
open CategoryTheory MonoidalCategory
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (π : X ⟶ Spec (.of K))

/-- Euler characteristic on a fixed two-chart cover is invariant under
isomorphism of sheaves. -/
theorem euler_iso (t : Probe π) {M N : t.curve.Modules} (e : M ≅ N) :
    t.euler M = t.euler N := by
  obtain ⟨𝒲, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso t.toBase t.toBase
      (Iso.refl t.curve) (by simp) t.cover N M
      (e ≪≫ ((Scheme.Modules.pullbackId t.curve).app N).symm)
  have h0' : 𝒲.U0 = t.cover.U0 := by simpa using h0
  have h1' : 𝒲.U1 = t.cover.U1 := by simpa using h1
  have hW : 𝒲 = t.cover := by
    have ext : ∀ A B : t.curve.TwoAffineOpenCover,
        A.U0 = B.U0 → A.U1 = B.U1 → A = B := by
      intro A B hA hB
      cases A
      cases B
      simp_all
    exact ext 𝒲 t.cover h0' h1'
  subst 𝒲
  unfold Probe.euler
  rw [e0.finrank_eq, e1.finrank_eq]

/-- Composing the map to the ambient scheme preserves the curve and its
chosen charts. -/
def postcomp (f : Y ⟶ X) (t : Probe (f ≫ π)) : Probe π where
  curve := t.curve
  toBase := t.toBase
  integral := t.integral
  proper := t.proper
  smooth := t.smooth
  toScheme := t.toScheme ≫ f
  over_base := by rw [Category.assoc, t.over_base]
  cover := t.cover

/-- The degree of a pushed-forward curve test equals the original test
on the pulled-back sheaf; this uses the actual pullback comparison. -/
theorem degree_postcomp (f : Y ⟶ X) (t : Probe (f ≫ π)) (M : X.Modules) :
    (postcomp π f t).degree M = t.degree ((Scheme.Modules.pullback f).obj M) := by
  change t.euler ((Scheme.Modules.pullback (t.toScheme ≫ f)).obj M) -
      t.euler (𝟙_ t.curve.Modules) =
    t.euler ((Scheme.Modules.pullback t.toScheme).obj
      ((Scheme.Modules.pullback f).obj M)) - t.euler (𝟙_ t.curve.Modules)
  exact congrArg (fun z : ℤ => z - t.euler (𝟙_ t.curve.Modules))
    (euler_iso (f ≫ π) t ((Scheme.Modules.pullbackComp t.toScheme f).app M)).symm

/-- A positive degree multiplier makes numerical triviality descend. -/
theorem numericalTrivial_of_multisections (f : Y ⟶ X)
    (hlift : ∀ t : Probe π, ∃ (s : Probe (f ≫ π)) (d : ℕ),
      0 < d ∧ ∀ M : X.Modules, Scheme.Modules.IsInvertible M →
        s.degree ((Scheme.Modules.pullback f).obj M) = (d : ℤ) * t.degree M)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hnum : NumericallyTrivial (f ≫ π) ((Scheme.Modules.pullback f).obj M)) :
    NumericallyTrivial π M := by
  intro t
  obtain ⟨s, d, hd, hdegree⟩ := hlift t
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hprod : (d : ℤ) * t.degree M = 0 := by
    rw [← hdegree M hM]
    exact hnum s
  exact (mul_eq_zero.mp hprod).resolve_left hd'

/-- Finite detection descends by taking the finite image of the curve
tests under composition, then applying numerical descent. -/
theorem finite_tests_of_cover (f : Y ⟶ X)
    (s : Finset (Probe (f ≫ π)))
    (hs : ∀ N : Y.Modules, Scheme.Modules.IsInvertible N →
      (∀ t ∈ s, t.degree N = 0) → NumericallyTrivial (f ≫ π) N)
    (hdesc : ∀ M : X.Modules, Scheme.Modules.IsInvertible M →
      NumericallyTrivial (f ≫ π) ((Scheme.Modules.pullback f).obj M) →
        NumericallyTrivial π M) :
    ∃ s : Finset (Probe π), ∀ M : X.Modules, Scheme.Modules.IsInvertible M →
      (∀ t ∈ s, t.degree M = 0) → NumericallyTrivial π M := by
  classical
  refine ⟨s.image (postcomp π f), ?_⟩
  intro M hM hzero
  apply hdesc M hM
  apply hs _ (hM.pullback f)
  intro t ht
  rw [← degree_postcomp π f t M]
  exact hzero _ (Finset.mem_image_of_mem _ ht)

end AlgebraicGeometry.CurveDegreeTests.Descent

open AlgebraicGeometry CategoryTheory
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ s : Finset (CurveDegreeTests.Probe π),
      ∀ M : X.Modules, Scheme.Modules.IsInvertible M →
        (∀ t ∈ s, t.degree M = 0) → CurveDegreeTests.NumericallyTrivial π M := by
  obtain ⟨Y, f, hfproper, hfsurj, hfsmooth, n, i, hi, hover⟩ :=
    exists_smooth_projective_surjective_cover_of_isProper K π
  letI := hfproper
  letI := hfsurj
  letI := hfsmooth
  letI := hi
  obtain ⟨s, hs⟩ :=
    RelPicard.exists_finite_curve_degree_tests_of_smooth_projective K (f ≫ π) n i hover
  apply CurveDegreeTests.Descent.finite_tests_of_cover π f s hs
  apply CurveDegreeTests.Descent.numericalTrivial_of_multisections π f
  intro t
  obtain ⟨s, g, hgfinite, hgsurj, hcomm, d, hd, hdegree⟩ :=
    CurveDegreeTests.exists_curve_degree_multisection K π f t
  exact ⟨s, d, hd, hdegree⟩
