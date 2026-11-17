-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensorPow_pointLogHeight_eq_nsmul_and_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:59.43638+00:00
-- url     : https://prove2.me/submissions/0d1e883a-25bd-4a72-9895-07bf02a09919

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_pointLogHeight_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensor_pointLogHeight_eq_add_and_isFinite
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- Positive canonical tensor powers retain a finite projective morphism. -/
theorem _root_.solution
    {K : Type} [Field K] [NumberField K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) (hP : IsFinite P.toProj) (n : ℕ) (hn : 0 < n) :
    ∃ (Nn : ℕ) (Rn : (M.tensorPow n).ProjPresentation f Nn),
      IsFinite Rn.toProj ∧ ∀ x : Scheme.KPoint f,
        Rn.pointLogHeight x = n * P.pointLogHeight x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  clear hn
  induction m with
  | zero =>
      obtain ⟨R, hto, hR⟩ := P.exists_iso_pointLogHeight_eq (λ_ M).symm
      refine ⟨N, R, ?_, fun x => ?_⟩
      · rwa [hto]
      · simpa only [Scheme.Modules.tensorPow, Nat.cast_one, one_mul] using hR x
  | succ m ih =>
      obtain ⟨Nm, Rm, hfin, hm⟩ := ih
      obtain ⟨idx, R, hRfin, hσ, hR⟩ :=
        Rm.exists_tensor_pointLogHeight_eq_add_and_isFinite P hfin
      refine ⟨_, R, hRfin, fun x => ?_⟩
      simpa only [Scheme.Modules.tensorPow_succ, Nat.cast_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        using (hR x).trans (congrArg (fun t : ℝ => t + P.pointLogHeight x) (hm x))

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
